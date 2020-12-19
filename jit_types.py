#!/usr/bin/python3
#-*- coding:utf8 -*-


import llvmlite.ir
import llvmlite.binding
import ctypes

__all__ = 'Module', 'Builder', 'Engine'



compiler_initialized = False


def initialize_compiler():
	global compiler_initialized
	llvmlite.binding.initialize()
	llvmlite.binding.initialize_native_target()
	llvmlite.binding.initialize_native_asmprinter()
	llvmlite.binding.initialize_native_asmparser()
	llvmlite.binding.initialize_all_targets()
	llvmlite.binding.initialize_all_asmprinters()
	compiler_initialized = True


def typeconv(lltype):
	if lltype == llvmlite.ir.IntType(1):
		return ctypes.c_bool
	elif lltype == llvmlite.ir.IntType(8):
		return ctypes.c_ubyte
	else:
		raise ValueError(str(lltype))


class Engine:
	def __init__(self, modules):
		if not compiler_initialized:
			initialize_compiler()
		target = llvmlite.binding.Target.from_default_triple()
		target_machine = target.create_target_machine()
		backing_mod = llvmlite.binding.parse_assembly("")
		self.engine = llvmlite.binding.create_mcjit_compiler(backing_mod, target_machine)
		self.modules = modules
		
		pmb = llvmlite.binding.PassManagerBuilder()
		pmb.opt_level = 3
		pm = llvmlite.binding.ModulePassManager()
		pmb.populate(pm)
		
		for module in self.modules:
			ll_module = llvmlite.binding.parse_assembly(str(module))
			pm.run(ll_module)
			self.engine.add_module(ll_module)
		self.engine.finalize_object()
	
	def __getattr__(self, name):
		addr = self.engine.get_function_address(name)
		
		ftype = None
		for module in self.modules:
			for function in module.module.functions:
				if str(function.name) == name:
					ftype = function.function_type
					break
			if ftype != None: break
		else:
			raise AttributeError
		
		cfunc = ctypes.CFUNCTYPE(typeconv(ftype.return_type), *[typeconv(_arg) for _arg in ftype.args])(addr)
		return cfunc
	
	def __enter__(self):
		self.engine.run_static_constructors()
	
	def __exit__(self, *arg):
		self.engine.run_static_destructors()


class Module:
	def __init__(self, name=''):
		self.module = llvmlite.ir.Module(name=name)
	
	def build_function(self, name, bits, arguments):
		return Builder(name, self.module, bits, arguments)
	
	def __str__(self):
		return str(self.module)
	
	def compile(self):
		return Engine([self])


class Builder:
	def __init__(self, name, module, bits, arguments):
		itype = llvmlite.ir.IntType(bits)
		func_type = llvmlite.ir.FunctionType(itype, (itype,) * len(arguments))
		func = llvmlite.ir.Function(module, func_type, name=name)
		block = func.append_basic_block('entry')
		builder = llvmlite.ir.IRBuilder(block)
		
		parent = self
		class Integer:
			def __init__(self, value, itype=None):
				
				if itype == None:
					try:
						self.itype = value.type
					except AttributeError:
						self.itype = parent.itype
				else:
					self.itype = itype
				
				try:
					if value.type != self.itype:
						value = self.itype(value)
				except AttributeError:
					value = self.itype(value)
				
				self.jit_value = value
			
			def __add__(self, other):
				try:
					second = other.jit_value
				except AttributeError:
					second = self.itype(other)
				
				return self.__class__(builder.add(self.jit_value, second))
			
			__radd__ = __add__
			
			def __sub__(self, other):
				try:
					second = other.jit_value
				except AttributeError:
					second = self.itype(other)
				
				return self.__class__(builder.sub(self.jit_value, second))
			
			def __mul__(self, other):
				try:
					second = other.jit_value
					return self.__class__(builder.mul(self.jit_value, second))
				except AttributeError:
					req_bits = 1 << other.bit_length().bit_length()
					if self.jit_value.type.width < req_bits:
						wide_type = llvmlite.ir.IntType(req_bits)
						first = builder.zext(self.jit_value, wide_type)
						second = wide_type(other)
					elif self.jit_value.type.width >= req_bits:
						first = self.jit_value
						second = self.jit_value.type(other)
					
					return self.__class__(builder.mul(first, second))
			
			__rmul__ = __mul__
			
			def __mod__(self, other):
				try:
					second = other.jit_value
					return self.__class__(builder.urem(self.jit_value, second))
				except AttributeError:
					req_bits = max(1 << ((other - 1).bit_length() - 1).bit_length(), 8)
					narrow_type = llvmlite.ir.IntType(req_bits)
					
					#print("mod", other, req_bits, (other - 1), ((other - 1).bit_length() - 1), ((other - 1).bit_length() - 1).bit_length())
					if other == 1 << self.jit_value.type.width:
						return self
					else:
						second = self.itype(other)
						m = builder.urem(self.jit_value, second)
						return self.__class__(builder.trunc(m, narrow_type), itype=narrow_type)
			
			def __and__(self, other):
				try:
					second = other.jit_value
				except AttributeError:
					second = self.itype(other)
				
				return self.__class__(builder.and_(self.jit_value, second))
			
			__rand__ = __and__
				
			def __or__(self, other):
				try:
					second = other.jit_value
				except AttributeError:
					second = self.itype(other)
				
				return self.__class__(builder.or_(self.jit_value, second))
			
			__ror__ = __or__
			
			def __xor__(self, other):
				try:
					if self.jit_value.type.width > other.jit_value.type.width:
						first = self.jit_value
						second = builder.zext(other.jit_value, self.jit_value.type)
					elif self.jit_value.type.width < other.jit_value.type.width:
						first = builder.zext(self.jit_value, other.jit_value.type)
						second = other.jit_value
					else:
						first = self.jit_value
						second = other.jit_value
					return self.__class__(builder.xor(first, second))
				except AttributeError:
					second = self.itype(other)
					return self.__class__(builder.xor(self.jit_value, second))
			
			__rxor__ = __xor__
			
			def __not__(self):
				return self.__class__(builder.not_(self.jit_value))
			
			def __lshift__(self, other):
				ext_type = llvmlite.ir.IntType(2 * self.itype.width)
				
				first = builder.zext(self.jit_value, ext_type)
				
				try:
					second = builder.zext(other.jit_value, ext_type)
				except AttributeError:
					second = ext_type(other)
				
				return self.__class__(builder.shl(first, second))
			
			def __rshift__(self, other):
				try:
					second = other.jit_value
					if self.itype != other.itype:
						second = self.itype(second)
				except AttributeError:
					second = self.itype(other)
				
				#print(self.itype, other.itype)
				
				return self.__class__(builder.lshr(self.jit_value, second))
			
			__bool__ = None
		
		self.itype = itype
		self.Integer = Integer
		self.builder = builder
		self.args = dict(zip(arguments, [Integer(_arg) for _arg in func.args]))
	
	def ret(self, value):
		try:
			jv = value.jit_value
		except AttributeError:
			jv = self.itype(value)
		self.builder.ret(jv)


if __debug__ and __name__ == '__main__':
	module = Module()
	add = module.build_function('adder', 8, ['x', 'y'])
	add.ret(add.args['x'] + add.args['y'] + 1)
	mul = module.build_function('muller', 8, ['x', 'y'])
	mul.ret(mul.args['x'] * mul.args['y'] + 2)
	engine = module.compile()
	print(engine.muller(10, 20))






