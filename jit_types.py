#!/usr/bin/python3
#-*- coding:utf8 -*-


import llvmlite.ir
import llvmlite.binding
from llvmlite.ir._utils import DuplicatedNameError
import ctypes


__all__ = 'Compiler', 'Code', 'Bitvector', 'Void', 'Bit', 'Byte', 'Short', 'Word', 'Long', 'HardwareType'



class Value:
	def __init__(self, type_, value):
		self.type_ = type_
		self.value = value
	
	@property
	def _as_parameter_(self):
		try:
			return self.c_parameter
		except AttributeError:
			pass
		
		if self.type_.length == None:
			result = self.type_.to_c_type()(*self.value)
		else:
			result = self.type_.to_c_type(False)(*self.value)
		
		self.c_parameter = result
		return result
	
	def __len__(self):
		return self.type_.length
	
	def __int__(self):
		return int(self._as_parameter_)
	
	def __getitem__(self, index):
		return self._as_parameter_[index]
	
	def to_llvm_constant(self):
		assert self.type_.length == len(self.value) if self.type_.length != None else True
		return llvmlite.ir.Constant(self.type_.to_llvm_type(False), self.value)


class Bitvector:
	def __init__(self, bits, length=None):
		self.bits = bits
		self.length = length
	
	def __getitem__(self, length):
		return self.__class__(self.bits, length)
	
	def __call__(self, *value):
		if self.length != None and len(value) > self.length:
			raise ValueError("Array initializer too long.")
		
		if self.length != None and len(value) != self.length and value[-1] != Ellipsis:
			raise ValueError("Array initializer too short.")
		
		if value[-1] == Ellipsis:
			value = value[:-1]
		
		return Value(self, value)
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + str(self.bits) + ', ' + str(self.length) + ')'
	
	def to_symbolic_type(self):
		if self.length != None:
			return Array
		elif self.bits:
			return Integer
		else:
			return Null
	
	def to_llvm_type(self, pointers):
		if self.length != None:
			if pointers:
				return llvmlite.ir.ArrayType(llvmlite.ir.IntType(self.bits), self.length).as_pointer()
			else:
				return llvmlite.ir.ArrayType(llvmlite.ir.IntType(self.bits), self.length)
		elif self.bits:
			return llvmlite.ir.IntType(self.bits)
		else:
			return llvmlite.ir.VoidType()
	
	def to_c_type(self, pointers):
		return typeconv(self.to_llvm_type(pointers), pointers)



Void = Bitvector(0)
Bit = Bitvector(1)
Byte = Bitvector(8)
Short = Bitvector(16)
Word = Bitvector(32)
Long = Bitvector(64)

def HardwareType(bits):
	if bits == 0:
		return Void
	elif bits == 1:
		return Bit
	elif 1 < bits <= 8:
		return Byte
	elif 8 < bits <= 16:
		return Short
	elif 16 < bits <= 32:
		return Word
	elif 32 < bits <= 64:
		return Long
	else:
		raise ValueError


compiler_initialized = False


def initialize_compiler():
	"Initialize the LLVM compiler."
	
	global compiler_initialized
	llvmlite.binding.initialize()
	llvmlite.binding.initialize_native_target()
	llvmlite.binding.initialize_native_asmprinter()
	llvmlite.binding.initialize_native_asmparser()
	llvmlite.binding.initialize_all_targets()
	llvmlite.binding.initialize_all_asmprinters()
	compiler_initialized = True


def finish_compiler():
	"Finish the compiler."
	
	global compiler_initialized
	compiler_initialized = False


def typeconv(lltype, pointers):
	"Convert an LLVM type to C type. Only limited subset of types is supported."
	
	try:
		if hasattr(lltype, 'pointee'):
			return ctypes.c_void_p
	except AttributeError:
		pass
	
	if lltype == llvmlite.ir.VoidType():
		return None
	elif lltype == llvmlite.ir.IntType(1):
		return ctypes.c_bool
	elif lltype == llvmlite.ir.IntType(8):
		return ctypes.c_ubyte
	elif lltype == llvmlite.ir.IntType(16):
		return ctypes.c_ushort
	
	try:
		if pointers:
			if hasattr(lltype, 'element') and hasattr(lltype, 'count'):
				return ctypes.c_void_p
		else:
			return typeconv(lltype.element, False) * lltype.count
	except AttributeError:
		pass
	
	raise ValueError(str(lltype))



class Code:
	"Compiled C code, from LLVM compiler. Compiled symbols are available under the attribute `symbol`. Symbols are guaranteed to be initialized only after entering the context."
	
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
				cfunc = ctypes.CFUNCTYPE(typeconv(ftype.return_type, False), *[typeconv(_arg, True) for _arg in ftype.args])(faddr)
				self.symbol[fname] = cfunc
			
			for glob in module.globals.values():
				if glob.name in self.symbol: continue
				gaddr = self.engine.get_global_value_address(glob.name)
				self.symbol[glob.name] = typeconv(glob.type, True)(gaddr)
	
	def __enter__(self):
		"Initalize certain C-level objects, such as global variables."
		self.engine.run_static_constructors()
	
	def __exit__(self, *arg):
		self.engine.run_static_destructors()






class Compiler:
	"The compiler, allowing compiling Python function to C and declaring C constants."
	
	def __init__(self, name=''):
		self.module = llvmlite.ir.Module(name=name)
		self.defined_functions = {}
		self.defined_globals = {}
	
	def __setitem__(self, name, constant):
		variable = llvmlite.ir.GlobalVariable(self.module, constant.type_.to_llvm_type(False), name)
		variable.initializer = constant.to_llvm_constant()
		variable.global_constant = True
		self.defined_globals[name] = variable
	
	def __getitem__(self, name):
		return Array(self.defined_globals[name])
	
	def function(self, name=None):
		def decorator(old_func):
			nonlocal name
			if name == None:
				name = old_func.__name__
			
			argtypes = [old_func.__annotations__[_arg] for _arg in old_func.__code__.co_varnames[:old_func.__code__.co_argcount]]
			rettype = old_func.__annotations__['return']
			functype = llvmlite.ir.FunctionType(rettype.to_llvm_type(False), [_argtype.to_llvm_type(True) for _argtype in argtypes])
			
			try:
				jit_func = llvmlite.ir.Function(self.module, functype, name=name)
				self.defined_functions[name] = jit_func
			except DuplicatedNameError:
				jit_func = self.defined_functions[name]
			
			block = jit_func.append_basic_block()
			builder = llvmlite.ir.IRBuilder(block)
			
			global current_builder
			try:
				old_builder = current_builder
				current_builder = builder
				
				result = old_func(*[_argtype.to_symbolic_type()(_arg) for (_argtype, _arg) in zip(argtypes, jit_func.args)])
				
				if result == None:
					if rettype.bits != 0:
						raise TypeError(f"The function returned no value despite declared as returning `{rettype}`.")
					builder.ret_void()
				elif hasattr(result, 'jit_value'):
					if rettype.to_llvm_type(False) != result.jit_value.type:
						raise TypeError(f"The function returned type `{result.jit_value.type}` incompatible from declared `{rettype}`.")
					builder.ret(result.jit_value)
				else:
					if rettype.bits == 0:
						raise TypeError(f"The function returned value `{result}` despite declared as returning void.")
					builder.ret(rettype.to_llvm_type(False)(result))
			
			except NotImplementedError:
				jit_func.blocks.remove(block)
			
			finally:
				current_builder = old_builder
			
			new_func = Function(jit_func, rettype, argtypes)
			new_func.__name__ = name
			return new_func
		
		return decorator
	
	def __str__(self):
		"LLVM assembler representation of the code compiled so far."
		return str(self.module)
	
	def compile(self):
		"Compile the LLVM module to C code."
		return Code([self.module])


current_builder = None

def get_builder():
	return current_builder


class Function:
	"An LLVM function object to be called from other Python functions that are to be compiled. Calling this object will create a call in the code."
	
	def __init__(self, func, rettype, argtypes):
		self.jit_func = func
		self.rettype = rettype
		self.argtypes = argtypes
	
	def __call__(self, *args):
		parms = []
		for argtype, arg in zip(self.argtypes, args):
			if argtype.length != None:
				parms.append(arg.jit_array)
			else:
				parms.append(arg.jit_value)
		result = get_builder().call(self.jit_func, parms)
		return self.rettype.to_symbolic_type()(result)


class Array:
	"Wrapper around an LLVM array. Can be used in Python code like a list."
	
	def __init__(self, array, bits=None):
		try:
			self.jit_array = array.jit_array
		except AttributeError:
			pass
		else:
			return
		
		if bits == None:
			self.jit_array = array
		else:
			self.jit_array = llvmlite.ir.ArrayType(llvmlite.ir.IntType(bits), array)
	
	def __getitem__(self, index):
		index = Integer(index, 16)
		builder = get_builder()
		return Integer(builder.load(builder.gep(self.jit_array, [Integer(0, 16).jit_value, index.jit_value])))
	
	def __setitem__(self, index, value):
		index = Integer(index, 16)
		value = Integer(value, self.jit_array.type.pointee.element.width)
		builder = get_builder()
		builder.store(value.jit_value, builder.gep(self.jit_array, [Integer(0, 16).jit_value, index.jit_value]))
	
	def __len__(self):
		return self.jit_array.type.pointee.count
	
	def __iter__(self):
		for n in range(len(self)):
			yield self[n]
	
	@property
	def _as_parameter_(self):
		return ctypes.pointer(typeconv(self.jit_array.type, False)(*[_x.constant for _x in self.jit_array.initializer.constant]))


class Integer:
	"Wrapper around an LLVM integer. Can be used like an integer in Python code."
	
	def __init__(self, value, bits=None):
		try:
			self.jit_value = value.jit_value
		except AttributeError:
			pass
		else:
			return
		
		if bits == None:
			assert hasattr(value, 'type') and hasattr(value.type, 'width')
			self.jit_value = value
		else:
			self.jit_value = llvmlite.ir.IntType(bits)(value)
	
	def bit_length(self):
		return self.jit_value.type.width
	
	def __add__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().add(self.jit_value, other.jit_value))
	
	__radd__ = __add__
	
	def __sub__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().sub(self.jit_value, other.jit_value))
	
	def __rsub__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().sub(other.jit_value, self.jit_value))
	
	def __mul__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().mul(self.jit_value, other.jit_value))
	
	__rmul__ = __mul__
	
	def __mod__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().urem(self.jit_value, other.jit_value))
	
	def __and__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().and_(self.jit_value, other.jit_value))
	
	__rand__ = __and__
	
	def __or__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().or_(self.jit_value, other.jit_value))
	
	__ror__ = __or__
	
	def __xor__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().xor(self.jit_value, other.jit_value))
	
	__rxor__ = __xor__
	
	def __neg__(self):
		return self.__class__(get_builder().not_(self.jit_value))
	
	def __lshift__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().shl(self.jit_value, other.jit_value))
	
	def __rshift__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().lshr(self.jit_value, other.jit_value))
	
	def __floordiv__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().sdiv(self.jit_value, other.jit_value))
	
	def __ne__(self, other):
		other = self.__class__(other, self.bit_length())
		return self.__class__(get_builder().icmp_unsigned('!=', self.jit_value, other.jit_value))
	
	__bool__ = None
	
	__hash__ = None
	
	@property
	def _as_parameter_(self):
		return typeconv(self.jit_value.type)(self.jit_value.constant)


class Null:
	def __init__(self, value=None):
		assert value == None
		self.jit_value = llvmlite.ir.VoidType()()




if __debug__ and __name__ == '__main__':
	compiler = Compiler()

	@compiler.function()
	def adder(x:Byte, y:Byte) -> Byte:
		return x + y
	
	@compiler.function()
	def muller(x:Byte, y:Byte) -> Byte:
		return x * y
	
	@compiler.function()
	def square(x:Byte) -> Byte:
		return muller(x, x)
	
	@compiler.function()
	def increment(x:Byte) -> Byte:
		raise NotImplementedError
	
	@compiler.function()
	def inc2(x:Byte) -> Byte:
		a = increment(x)
		b = increment(a)
		return b
	
	@compiler.function()
	def increment(x:Byte) -> Byte:
		return x + 1
	
	@compiler.function()
	def return_const() -> Byte:
		return 1
	
	'''
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
	'''
	
	compiler['zero_vec'] = Byte[4](0, 0, 0, 0)
	compiler['one_vec'] = Byte[4](1, 0, 0, 0)
	compiler['one_prim_vec'] = Byte[4](0, 1, 0, 0)
	compiler['series_vec'] = Byte[4](4, 3, 2, 1)
	
	one_prim_vec = compiler['one_prim_vec']
	
	@compiler.function()
	def summer(a:Byte[4]) -> Byte:
		return a[0] + a[1] + a[2] + a[3]
	
	@compiler.function()
	def scalar_product(a:Byte[4], b:Byte[4]) -> Byte:
		r = 0
		for n in range(4):
			r += a[n] * b[n]
		return r
	
	@compiler.function()
	def static_selector(a:Byte[4]) -> Byte:
		r = 0
		for n in range(4):
			r += a[n] * one_prim_vec[n]
		return r
	
	@compiler.function()
	def output_array(a:Byte[6]) -> Void:
		for n in range(len(a)):
			a[n] = n
	
	#print(compiler)
	
	code = compiler.compile()
	
	for name, function in code.symbol.items():
		locals()[name] = function
	
	with code:
		assert adder(2, 2) == 4
		assert adder(250, 5) == 255
		assert adder(250, 6) == 0
		
		assert muller(2, 3) == 6
		assert square(4) == 16
		
		assert increment(7) == 8
		assert inc2(8) == 10
		
		assert return_const() == 1
		
		'''
		assert divide_by_zero(99) == 0
		assert subber(1, 2) == 255
		assert rshifter(255) == 0b1111111
		assert lshifter(1) == 0b10
		assert ander(47, 23) == 47 & 23
		assert orer(47, 23) == 47 | 23
		assert xorer(47, 23) == 47 ^ 23
		'''
		
		six_times_four = Byte[4](6, 6, 6, 6)
		assert summer(six_times_four) == 24
		assert summer(Byte[4](5, 5, 5, 5)) == 20
		assert summer(zero_vec) == 0
		assert summer(one_vec) == 1
		assert summer(one_prim_vec) == 1
		assert summer(series_vec) == 10
		
		assert scalar_product(zero_vec, zero_vec) == 0
		assert scalar_product(one_vec, one_vec) == 1
		assert scalar_product(one_vec, one_prim_vec) == 0
		assert scalar_product(one_prim_vec, one_vec) == 0
		assert scalar_product(one_vec, series_vec) == 4
		assert scalar_product(one_prim_vec, series_vec) == 3
		assert scalar_product(series_vec, series_vec) == 1 + 4 + 9 + 16
		
		assert static_selector(series_vec) == 3
		
		buf = Byte[6](...)
		output_array(buf)
		assert all(buf[_n] == _n for _n in range(len(buf)))





