#!/usr/bin/python3


import fields
import linear
from tracing import SymbolicValue, trace, build_array
from llvmlite.ir import VoidType, IntType, ArrayType, FunctionType, Constant, GlobalVariable, Function, Module, IRBuilder
import inspect


def compile_field(module, symbols, short_t, long_t):
	class Field(fields.Galois('Field', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])):
		def serialize(self):
			yield self._BinaryGalois__value
		
		def _to_symbolic(self):
			return SymbolicValue(self._BinaryGalois__value)
	
	symbols['Field.exponent'] = build_array(Field.exponent, module, 'Field.exponent', short_t)
	symbols['Field.logarithm'] = build_array(Field.logarithm, module, 'Field.logarithm', short_t)
	Field.logarithm = SymbolicValue.make_global('Field.logarithm')
	Field.exponent = SymbolicValue.make_global('Field.exponent')
	
	trace(Field.__add__, module, symbols, {int:long_t, Field:short_t}, Field, 'Field.__add__')
	trace(Field.__sub__, module, symbols, {int:long_t, Field:short_t}, Field, 'Field.__sub__')
	trace(Field.__neg__, module, symbols, {int:long_t, Field:short_t}, Field, 'Field.__neg__')
	trace(Field.__mul__, module, symbols, {int:long_t, Field:short_t}, Field, 'Field.__mul__')
	trace(Field.__truediv__, module, symbols, {int:long_t, Field:short_t}, Field, 'Field.__truediv__')
	trace(Field.__pow__, module, symbols, {int:long_t, Field:short_t}, Field, 'Field.__pow__')
	
	return Field


def compile_linear(module, symbols, short_t, long_t, oField):
	class Linear(linear.Linear):
		class Field(oField):
			def __init__(self, value):
				self.value = value
			
			def serialize(self):
				yield self.value
			
			def _to_symbolic(self):
				return SymbolicValue(self.value)
			
			__add__ = SymbolicValue.make_global('Field.__add__')
			__sub__ = SymbolicValue.make_global('Field.__sub__')
			__neg__ = SymbolicValue.make_global('Field.__neg__')
			__mul__ = SymbolicValue.make_global('Field.__mul__')
			__truediv__ = SymbolicValue.make_global('Field.__truediv__')
			__pow__ = SymbolicValue.make_global('Field.__pow__')
		
		@staticmethod
		def Array(a, b, c):
			print("Array:", type(a))
			l = []
			for e in a:
				print("el:", e)
				l.append(e)
			return l
		
		def _to_symbolic(self):
			return SymbolicValue.make_list([_v for _v in self._Linear__f])
	
	array_t = ArrayType(short_t, Field.field_power).as_pointer()
	
	trace(Linear.__add__, module, symbols, {int:long_t, Linear:array_t}, Linear, 'Linear.__add__')


if __debug__ and __name__ == '__main__':
	from pathlib import Path
	
	short_t = IntType(8)
	long_t = IntType(16)
	
	Path('compiled').mkdir(exist_ok=True)
	
	symbols = {}
	
	module = Module()
	Field = compile_field(module, symbols, short_t, long_t)
	#Path('compiled/fields.ll').write_text(str(module), encoding='utf-8')
	
	module = Module()
	compile_linear(module, symbols, short_t, long_t, Field)
	#Path('compiled/linear.ll').write_text(str(module), encoding='utf-8')
	print(module)
	



