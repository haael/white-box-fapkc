#!/usr/bin/python3
#-*- coding:utf8 -*-


import llvmlite.ir
import llvmlite.binding
from llvmlite.ir._utils import DuplicatedNameError
import ctypes


__all__ = 'Compiler', 'Code', 'Function', 'Integer', 'Array'


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


def finish_compiler():
	global compiler_initialized
	compiler_initialized = False


def typeconv(lltype):
	if lltype == llvmlite.ir.IntType(1):
		return ctypes.c_bool
	elif lltype == llvmlite.ir.IntType(8):
		return ctypes.c_ubyte
	elif lltype == llvmlite.ir.IntType(16):
		return ctypes.c_ushort
	else:
		raise ValueError(str(lltype))


class Code:
	def __init__(self, modules):
		if not compiler_initialized:
			initialize_compiler()
		target = llvmlite.binding.Target.from_default_triple()
		target_machine = target.create_target_machine()
		backing_mod = llvmlite.binding.parse_assembly("")
		self.engine = llvmlite.binding.create_mcjit_compiler(backing_mod, target_machine)
		
		pmb = llvmlite.binding.PassManagerBuilder()
		pmb.opt_level = 3
		pm = llvmlite.binding.ModulePassManager()
		pmb.populate(pm)
		
		self.modules = []
		for module in modules:
			ll_module = llvmlite.binding.parse_assembly(str(module))
			pm.run(ll_module)
			self.engine.add_module(ll_module)
		self.modules.append(ll_module)
		self.engine.finalize_object()
		
		self.symbol = {}
		for module in modules:
			for function in module.functions:
				fname = function.name
				ftype = function.function_type
				faddr = self.engine.get_function_address(fname)
				cfunc = ctypes.CFUNCTYPE(typeconv(ftype.return_type), *[typeconv(_arg) for _arg in ftype.args])(faddr)
				self.symbol[fname] = cfunc
	
	def __enter__(self):
		self.engine.run_static_constructors()
	
	def __exit__(self, *arg):
		self.engine.run_static_destructors()


class Array:
	def __init__(self, array):
		self.array = array
	
	def __getitem__(self, item):
		builder = get_builder()
		index = builder.zext(Integer(item).jit_value, llvmlite.ir.IntType(16))
		return Integer(builder.load(builder.gep(self.array, [Integer(0).jit_value, index]))) # TODO: overflow


class Compiler:
	def __init__(self, name=''):
		self.module = llvmlite.ir.Module(name=name)
		self.defined_functions = {}
	
	def array(self, name, bits, elements):
		itype = llvmlite.ir.IntType(bits)
		value = llvmlite.ir.Constant.literal_array([itype(_el) for _el in elements])
		variable = llvmlite.ir.GlobalVariable(self.module, value.type, name)
		variable.initializer = value
		variable.global_constant = True
		return Array(variable)
	
	def function(self, bits, arg_count=None, name=None):
		return lambda callback: self.declare_function(name, arg_count, bits, callback)
	
	def declare_function(self, name, arg_count, bits, callback=None):
		try:
			if name == None:
				name = callback.__name__
			
			if arg_count == None:
				arg_count = callback.__code__.co_argcount
		except AttributeError:
			raise ValueError("If `arg_count` or `name` is undefined, then `callback` must be a valid Python function.")
		
		itype = llvmlite.ir.IntType(bits)
		
		func_type = llvmlite.ir.FunctionType(itype, (itype,) * arg_count)
		
		try:
			func = llvmlite.ir.Function(self.module, func_type, name=name)
			self.defined_functions[name] = func
		except DuplicatedNameError:
			func = self.defined_functions[name]
		
		if callback != None:
			block = func.append_basic_block()
			builder = llvmlite.ir.IRBuilder(block)
			
			global current_builder
			try:
				old_builder = current_builder
				current_builder = builder
				result = callback(*[Integer(_arg) for _arg in func.args])
				if result == None:
					builder.ret(llvmlite.ir.VoidType()())
				else:
					try:
						builder.ret(result.jit_value)
					except AttributeError:
						builder.ret(llvmlite.ir.IntType(bits)(result))
			finally:
				current_builder = old_builder
		
		fn_object = Function(func, arg_count)
		fn_object.__name__ = name
		return fn_object
	
	def __str__(self):
		return str(self.module)
	
	def compile(self):
		return Code([self.module])


current_builder = None

def get_builder():
	return current_builder


class Function:
	def __init__(self, func, arg_count):
		self.func = func
		self.arg_count = arg_count
	
	def __call__(self, *args):
		if len(args) != self.arg_count:
			raise TypeError
		builder = get_builder()
		result = builder.call(self.func, [_arg.jit_value for _arg in args])
		return Integer(result)


class Integer:
	def __init__(self, value):
		try:
			self.jit_value = value.jit_value
			return
		except AttributeError:
			pass
		
		try:
			bits = self.round_8(value.bit_length())
			self.jit_value = llvmlite.ir.IntType(bits)(value)
			return
		except AttributeError:
			pass
		
		self.jit_value = value

		if self.jit_value.type.width > self.max_bits: raise ValueError("Maximum bit width exceeded")
	
	max_bits = 64
	
	@staticmethod
	def round_8(i):
		return 1 << (i - 1).bit_length() if i >= 8 else 8
		#return 8 * ( ((i - 1) // 8 + 1) ) if i > 1 else 8
	
	def bit_length(self):
		return self.jit_value.type.width
	
	def upper_bound(self):
		try:
			return self.jit_value.constant
		except AttributeError:
			return (1 << self.bit_length()) - 1
	
	def __add__(self, other):
		other = self.__class__(other)
		bits = self.round_8(max(self.bit_length(), other.bit_length()) + 1)
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.add(first, second))
	
	__radd__ = __add__
	
	def __sub__(self, other):
		other = self.__class__(other)
		bits = self.round_8(max(self.bit_length(), other.bit_length()))
		if bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.sub(first, second))
	
	def __rsub__(self, other):
		other = self.__class__(other)
		bits = self.round_8(max(self.bit_length(), other.bit_length()))
		if bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.sub(second, first))
	
	def __mul__(self, other):
		other = self.__class__(other)
		bits = self.round_8(self.bit_length() + other.bit_length())
		if bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.mul(first, second))
	
	__rmul__ = __mul__
	
	def __mod__(self, other):
		other = self.__class__(other)
		
		arg_bits = self.round_8(max(self.bit_length(), other.bit_length()))
		if arg_bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		arg_type = llvmlite.ir.IntType(arg_bits)
		
		result_bits = self.round_8((other.upper_bound() - 1).bit_length())
		if result_bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		result_type = llvmlite.ir.IntType(result_bits)
		
		builder = get_builder()
		
		# TODO: division by zero
		
		first = self.jit_value
		if self.bit_length() < arg_bits:
			try:
				first = arg_type(first.constant)
			except AttributeError:
				first = builder.zext(first, arg_type)
		
		second = other.jit_value
		if other.bit_length() < arg_bits:
			try:
				second = arg_type(second.constant)
			except AttributeError:
				second = builder.zext(second, arg_type)
		
		result = self.__class__(builder.urem(first, second))
		if result.bit_length() > result_bits:
			result = self.__class__(builder.trunc(result.jit_value, result_type))
		return result
	
	def __and__(self, other):
		other = self.__class__(other)
		bits = self.round_8(min(self.bit_length(), other.bit_length()))
		if bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() > bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.trunc(first, result_type)
		
		second = other.jit_value
		if other.bit_length() > bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.trunc(second, result_type)
		
		try:
			if second.constant + 1 == 1 << bits:
				return self.__class__(first)
		except AttributeError:
			pass
		
		try:
			if first.constant + 1 == 1 << bits:
				return self.__class__(second)
		except AttributeError:
			pass
		
		return self.__class__(builder.and_(first, second))
	
	__rand__ = __and__
	
	def __or__(self, other):
		other = self.__class__(other)
		bits = self.round_8(max(self.bit_length(), other.bit_length()))
		if bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.or_(first, second))
	
	__ror__ = __or__
	
	def __xor__(self, other):
		other = self.__class__(other)
		bits = self.round_8(max(self.bit_length(), other.bit_length()))
		if bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.xor(first, second))
	
	__rxor__ = __xor__
	
	def __neg__(self):
		return self.__class__(builder.not_(self.jit_value))
	
	def __lshift__(self, other):
		other = self.__class__(other)
		bits = self.round_8(self.bit_length() + other.upper_bound())
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.shl(first, second))
	
	def __rshift__(self, other):
		other = self.__class__(other)
		bits = self.round_8(max(self.bit_length(), other.bit_length()))
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.lshr(first, second))
	
	def __floordiv__(self, other):
		other = self.__class__(other)
		bits = self.round_8(max(self.bit_length(), other.bit_length()))
		if bits > self.max_bits: raise ValueError("Maximum bit width exceeded")
		result_type = llvmlite.ir.IntType(bits)
		
		builder = get_builder()
		
		# TODO: division by zero
		#with builder.if_then(other.jit_value == other.type(0)):
		#	raise_exception
		
		first = self.jit_value
		if self.bit_length() < bits:
			try:
				first = result_type(first.constant)
			except AttributeError:
				first = builder.zext(first, result_type)
		
		second = other.jit_value
		if other.bit_length() < bits:
			try:
				second = result_type(second.constant)
			except AttributeError:
				second = builder.zext(second, result_type)
		
		return self.__class__(builder.sdiv(first, second))
	
	def __ne__(self, other):
		other = self.__class__(other)
		builder = get_builder()
		return self.__class__(builder.icmp_unsigned('!=', self.jit_value, other.jit_value))
	
	__bool__ = None
	
	__hash__ = None


if __debug__ and __name__ == '__main__':
	compiler = Compiler()
	
	increment = compiler.declare_function('increment', arg_count=1, bits=8)
	
	@compiler.function(bits=8)
	def inc2(x):
		a = increment(x)
		b = increment(a)
		return b
	
	@compiler.function(bits=8)
	def adder(x, y):
		return (x + y) & 255
	
	@compiler.function(bits=8)
	def muller(x, y):
		return (x * y) & 255
	
	@compiler.function(bits=8)
	def square(x):
		return muller(x, x)
	
	@compiler.function(bits=8)
	def increment(x):
		return (x + 1) & 255
	
	@compiler.function(bits=8)
	def divide_by_zero(x):
		return x // 0
	
	@compiler.function(bits=8)
	def subber(x, y):
		return x - y
	
	@compiler.function(bits=8)
	def rshifter(x):
		return x >> 1
	
	@compiler.function(bits=8)
	def lshifter(x):
		return (x << 1) & 255

	@compiler.function(bits=8)
	def ander(x, y):
		return x & y
	
	@compiler.function(bits=8)
	def orer(x, y):
		return x | y
	
	@compiler.function(bits=8)
	def xorer(x, y):
		return x ^ y
	

	
	print(compiler)
	
	code = compiler.compile()
	
	for name, function in code.symbol.items():
		locals()[name] = function
	
	with code:
		assert adder(2, 2) == 4
		assert muller(2, 3) == 6
		assert square(4) == 16
		assert increment(7) == 8
		assert inc2(8) == 10
		assert divide_by_zero(99) == 0
		assert subber(1, 2) == 255
		assert rshifter(255) == 0b1111111
		assert lshifter(1) == 0b10
		assert ander(47, 23) == 47 & 23
		assert orer(47, 23) == 47 | 23
		assert xorer(47, 23) == 47 ^ 23





