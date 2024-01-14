#!/usr/bin/python3


import fields
import linear
import machines
from tracing import SymbolicValue, transform
from llvmlite.ir import VoidType, IntType, ArrayType, FunctionType, Constant, GlobalVariable, Function, Module, IRBuilder
import inspect


def compile_constant(module, int_t, const):
	return int_t(const)


def compile_array(module, int_t, name, table):
	array_t = ArrayType(int_t, len(table))
	result = GlobalVariable(module, array_t, name)
	result.initializer = array_t([int_t(int(_n)) for _n in table])
	result.global_constant = True
	return result


def compile_function(module, short_t, long_t, symcls, name, func, compiled):
	arg_len = len(inspect.getfullargspec(func).args)
	
	def fn(*args):
		return func(*[symcls(_arg) for _arg in args])
	
	symbols = {'func':func, 'symcls':symcls}
	_, lfn = transform(fn, module, short_t, long_t, name, arg_len, symbols, compiled)
	
	return lfn


arithmetic_methods = frozenset([
	'__neg__', '__add__', '__sub__', '__mul__', '__matmul__', '__truediv__', '__floordiv__', '__mod__', '__divmod__', #'__pow__',
	'__radd__', '__rsub__', '__rmul__', '__rmatmul__', '__rtruediv__', '__rfloordiv__', '__rmod__', '__rdivmod__'#, '__rpow__'
])


def compile_class(module, short_t, long_t, classname, cls):
	compiled = {}
	symbolic = {}
	
	for name in dir(cls):
		symbol = getattr(cls, name)
		
		if symbol is None or isinstance(symbol, property | classmethod | type):
			pass
		elif name.startswith('__') and name not in arithmetic_methods:
			pass
		elif callable(symbol):
			pass
		elif isinstance(symbol, tuple | list):
			compiled[classname + '.' + name] = compile_array(module, short_t, classname + '.' + name, symbol)
			symbolic[name] = SymbolicValue.make_global(classname + '.' + name)
		elif isinstance(symbol, int):
			compiled[classname + '.' + name] = compile_constant(module, long_t, symbol)
			symbolic[name] = SymbolicValue.make_global(classname + '.' + name)
		else:
			raise NotImplementedError(name + " / " + symbol.__class__.__name__)
	
	symcls = type(classname, (cls,), symbolic)
	
	for name in dir(cls):
		symbol = getattr(cls, name)
		
		if symbol is None or isinstance(symbol, property | classmethod | type):
			pass
		elif name not in arithmetic_methods:
			pass
		elif callable(symbol):
			compiled[classname + '.' + name] = compile_function(module, short_t, long_t, symcls, classname + '.' + name, symbol, compiled)
			symbolic[name] = SymbolicValue.make_global(classname + '.' + name)
		else:
			pass
	
	return type(classname, (), symbolic)


def compile_field(module, short_t, long_t):
	def serialize(val):
		#print("serialize:", repr(val.__dict__))
		yield val._BinaryGalois__value
	
	ofield = fields.Galois('Field', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	ofield = type('Field', (ofield,), {'serialize':serialize})
	
	return compile_class(module, short_t, long_t, 'Field', ofield)


def compile_linear(module, short_t, long_t, Field):
	return compile_class(module, short_t, long_t, 'Linear', linear.Linear)


if __debug__ and __name__ == '__main__':
	module = Module()
	
	short_t = IntType(8)
	long_t = IntType(16)
	
	Field = compile_field(module, short_t, long_t)
	#Linear = compile_linear(module, short_t, long_t, Field)
	
	print(module)



