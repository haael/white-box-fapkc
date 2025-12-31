#!/usr/bin/python3


from enum import Enum
from itertools import chain, product, zip_longest
import ast
import inspect
from ctypes import pythonapi, py_object, c_int
from functools import reduce
from operator import __mul__
#from llvmlite import ir, binding
from collections import Counter, defaultdict
from collections.abc import Iterable, Sequence
from typing import Self, Generator, Iterator, Any
from utils import *
from dis import get_instructions
from types import FunctionType, NoneType, SimpleNamespace


class BooleanTest(BaseException):
	pass


class LoopIteration(BaseException):
	pass


boolean_tests = dict()
active_loops = set()


class Comparator:
	def __init__(self, expression):
		self.expression = expression
		if not isinstance(self.expression, SymbolicExpression):
			raise ValueError(f"Argument should be SymbolicExpression, got {type(self.expression).__name__}.")
	
	def __eq__(self, other):
		try:
			if self.expression.operator != other.expression.operator:
				return False
			
			if hash(self) != hash(other):
				return False
			
			try:
				if len(self.expression.operands) != len(other.expression.operands):
					return False
				
				for op1, op2 in zip(self.expression.operands, other.expression.operands):
					if isinstance(op1, SymbolicExpression):
						op1 = self.__class__(op1)
					
					if isinstance(op2, SymbolicExpression):
						op2 = self.__class__(op2)
					
					if op1 != op2:
						return False
			except TypeError:
				if self.expression.operands != other.expression.operands:
					return False
			
			return True
		
		except AttributeError:
			return NotImplemented
	
	@cached
	def __hash__(self):
		return self.expression._hash()
	
	def __str__(self):
		return str(self.expression)
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + repr(self.expression) + ')'


class SymbolicExpression:
	"Herbrand model of Python computation. Common methods."
	
	def __init__(self, operator, operands=None):
		#print(operator.__class__.__name__)
		if operator.__class__.__name__ == 'Operator' and operands is None:
			raise ValueError("If `operator` is an Operator then `operands` must not be None.")
		
		#if self.__class__ == SymbolicList:
		#	print("constructing list", operator, operands)
		#	if operator == SymbolicList.Operator.FOR:
		#		for op in operands:
		#			if isinstance(op, SymbolicList):
		#				assert hasattr(op, 'operator') and hasattr(op, 'operands')
		
		if operands is None:
			try:
				self.operator = operator.operator
				self.operands = operator.operands
			except AttributeError:
				assert not isinstance(operator, SymbolicExpression)
				const = self._const(operator)
				assert hasattr(const, 'operator') and hasattr(const, 'operands')
				self.operator = const.operator
				self.operands = const.operands
		else:
			self.operator = operator
			self.operands = operands
		
		assert hasattr(self, 'operator') and hasattr(self, 'operands')
		
		if not isinstance(self.operator, self.Operator):
			raise TypeError(f"`operator` must be {self.Operator}, got {type(operator)}.")
		
		if __debug__:
			"Make sure all operands are hashable."
			if self.operator == SymbolicList.Operator.LIST:
				l, n = self.operands
				if isinstance(n, Generator):
					raise TypeError("Generators can not be elements of symbolic expression.")
				hash(n)
				for item in l:
					if not isinstance(item, SymbolicExpression):
						if isinstance(item, Generator):
							raise TypeError("Generators can not be elements of symbolic expression.")
						hash(item)
			elif isinstance(self.operands, list|tuple):
				for operand in self.operands:
					if isinstance(operand, Generator):
						raise TypeError("Generators can not be elements of symbolic expression.")
					if not isinstance(operand, SymbolicExpression):
						hash(operand)
			else:
				if isinstance(self.operands, Generator):
					raise TypeError("Generators can not be elements of symbolic expression.")
				hash(self.operands)
	
	def _print(self, level=0):
		yield level, str(self.operator)
		if isinstance(self.operands, list|tuple):
			for op in self.operands:
				if hasattr(op, '_print'):
					yield from op._print(level + 1)
				else:
					yield level + 1, str(op)
		else:
			yield level + 1, str(self.operands)
	
	def _hash(self):
		ops = [self.operator]
		try:
			for op in self.operands:
				try:
					oph = op._hash()
				except AttributeError:
					oph = hash(op)
				ops.append(oph)
		
		except TypeError:
			try:
				oph = self.operands._hash()
			except AttributeError:
				#print("hash", self.operands)
				oph = hash(self.operands)
			ops.append(oph)
		
		return hash(tuple(ops))
	
	__hash__ = _hash
	
	def __str__(self):
		return " ".join(_b for (_a, _b) in self._print())
	
	def __repr__(self):
		if not hasattr(self, 'operator') or not hasattr(self, 'operands'):
			return f'<Unfinished {self.__class__.__name__}>'
		return self.__class__.__name__ + '(' + self.operator.__class__.__name__ + '.' + self.operator.name + ', ' + repr(self.operands) + ')'
	
	def __eq__(self, other):
		if other.__class__.__name__ == 'Operator':
			return NotImplemented
		other = self.__class__(other)
		return SymbolicBool(SymbolicBool.Operator.EQ, (self, other))
	
	def __ne__(self, other):
		other = self.__class__(other)
		return SymbolicBool(SymbolicBool.Operator.NE, (self, other))
	
	def __ge__(self, other):
		other = self.__class__(other)
		return SymbolicBool(SymbolicBool.Operator.GE, (self, other))
	
	def __le__(self, other):
		other = self.__class__(other)
		return SymbolicBool(SymbolicBool.Operator.LE, (self, other))
	
	def __gt__(self, other):
		other = self.__class__(other)
		return SymbolicBool(SymbolicBool.Operator.GT, (self, other))
	
	def __lt__(self, other):
		other = self.__class__(other)
		return SymbolicBool(SymbolicBool.Operator.LT, (self, other))
	
	def __bool__(self):
		raise NotImplementedError
	
	def _has_for(self):
		if isinstance(self.operands, list|tuple):
			return any(_op._has_for() for _op in self.operands if hasattr(_op, '_has_for'))
		return False

	def evaluate(self, args):
		raise NotImplementedError(f"SymbolicExpression(operator={self.operator.name}, operands={self.operands}).evaluate")


class SymbolicBool(SymbolicExpression):
	"Herbrand model of Python computation. Symbolic `bool` value."
	
	class Operator(Enum):
		BOOL = 'bool'
		
		EQ = '=='
		NE = '!='
		GE = '>='
		LE = '<='
		GT = '>'
		LT = '<'
		
		NOT = 'not'
		AND = 'and'
		OR = 'or'
		XOR = 'xor'	
	
	@classmethod
	def _const(cls, value):
		return cls(cls.Operator.BOOL, bool(value))
		
	def __bool__(self):
		cmp = Comparator(self)
		try:
			return boolean_tests[cmp]
		except KeyError:
			raise BooleanTest(cmp)
	
	def __not__(self):
		return self.__class__(self.Operator.NOT, (self,))
	
	def __and__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.AND, (self, other))
	
	def __rand__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.AND, (other, self))
	
	def __or__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.OR, (self, other))
	
	def __ror__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.OR, (other, self))
	
	def __xor__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.XOR, (self, other))
	
	def __rxor__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.XOR, (other, self))
	
	'''
	def compile(self, builder, loop_vars):
		if self.operator == self.Operator.BOOL:
			return ir.Constant(self.ll_type, self.operands)
		elif self.operator == SymbolicInt.Operator.AND:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.and_(*operands)
		elif self.operator == self.Operator.OR:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.or_(*operands)
		elif self.operator == self.Operator.XOR:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.xor(*operands)
		elif self.operator == self.Operator.NOT:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.not_(*operands)
		elif self.operator == self.Operator.EQ:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.icmp_unsigned('==', *operands)
		elif self.operator == self.Operator.NE:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.icmp_unsigned('!=', *operands)
		elif self.operator == self.Operator.GE:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.icmp_unsigned('>=', *operands)
		elif self.operator == self.Operator.LE:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.icmp_unsigned('<=', *operands)
		elif self.operator == self.Operator.GT:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.icmp_unsigned('>', *operands)
		elif self.operator == self.Operator.LT:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.icmp_unsigned('<', *operands)
		else:
			raise NotImplementedError(f"Unsupported operator: {self.operator}")
	'''
	
	def evaluate(self, args):
		if self.operator == self.Operator.EQ:
			x, y = self.operands
			return x.evaluate(args) == y.evaluate(args)
		elif self.operator == self.Operator.NE:
			x, y = self.operands
			return x.evaluate(args) != y.evaluate(args)
		elif self.operator == self.Operator.GT:
			x, y = self.operands
			return x.evaluate(args) > y.evaluate(args)
		elif self.operator == self.Operator.LT:
			x, y = self.operands
			return x.evaluate(args) < y.evaluate(args)
		elif self.operator == self.Operator.GE:
			x, y = self.operands
			return x.evaluate(args) >= y.evaluate(args)
		elif self.operator == self.Operator.LE:
			x, y = self.operands
			return x.evaluate(args) <= y.evaluate(args)
		elif self.operator == self.Operator.BOOL:
			n = self.operands
			return n
		else:
			raise NotImplementedError(f"SymbolicBool(operator={self.operator.name}, operands={self.operands}).evaluate")


class SymbolicInt(SymbolicExpression):
	"Herbrand model of Python computation. Symbolic `int` value."
	
	class Operator(Enum):
		INT = 'int'
		ARG = 'int_arg'
		FOR = 'int_for'
		LEN = 'len'
		ITEM = 'item'
		CALL = 'call'
		
		NEG = '(-)'
		ADD = '+'
		SUB = '-'
		MUL = '*'
		MOD = '%'
		FLOORDIV = '//'
		
		NOT = '~'
		AND = '&'
		OR = '|'
		XOR = '^'
	
	@classmethod
	def _const(cls, value):
		return cls(cls.Operator.INT, int(value))
	
	@classmethod
	def _arg(cls, number):
		return cls(cls.Operator.ARG, number)
	
	@classmethod
	def _for(cls, loop_id, name, value):
		if not isinstance(value, cls) and value is not Ellipsis:
			value = cls._const(value)
		return cls(cls.Operator.FOR, (loop_id, name, value))
	
	@classmethod
	def _len(cls, seq):
		return cls(cls.Operator.LEN, (seq,))
	
	@classmethod
	def _item(cls, seq, index):
		return cls(cls.Operator.ITEM, (seq, index))
	
	@classmethod
	def _call(cls, funcname, varname, args):
		return cls(cls.Operator.CALL, (funcname, varname, args))
	
	def __bool__(self):
		return bool(self == 0)
	
	def __neg__(self):
		return self.__class__(self.Operator.NEG, (self,))
	
	def __add__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.ADD, (self, other))
	
	def __radd__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.ADD, (other, self))
	
	def __sub__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.SUB, (self, other))
	
	def __rsub__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.SUB, (other, self))
	
	def __mul__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.MUL, (self, other))
	
	def __rmul__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.MUL, (other, self))
	
	def __mod__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.MOD, (self, other))
	
	def __rmod__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.MOD, (other, self))
	
	def __floordiv__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.FLOORDIV, (self, other))
	
	def __rfloordiv__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.FLOORDIV, (other, self))
	
	def __not__(self):
		return self.__class__(self.Operator.NOT, (self,))
	
	def __and__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.AND, (self, other))
	
	def __rand__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.AND, (other, self))
	
	def __or__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.OR, (self, other))
	
	def __ror__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.OR, (other, self))
	
	def __xor__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.XOR, (self, other))
	
	def __rxor__(self, other):
		other = self.__class__(other)
		return self.__class__(self.Operator.XOR, (other, self))
	
	'''
	def compile(self, builder, loop_vars):
		if self.operator == self.Operator.INT:
			return ir.Constant(self.ll_type, self.operands)
		elif self.operator == self.Operator.FOR:
			return loop_vars[tuple(self.operands[0:2])]
		elif self.operator == self.Operator.ARG:
			return builder.function.args[self.operands]
		elif self.operator == self.Operator.AND:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.and_(*operands)
		elif self.operator == self.Operator.OR:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.or_(*operands)
		elif self.operator == self.Operator.XOR:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.xor(*operands)
		elif self.operator == self.Operator.NOT:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.not_(*operands)
		elif self.operator == self.Operator.ADD:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.add(*operands)
		elif self.operator == self.Operator.SUB:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.sub(*operands)
		elif self.operator == self.Operator.MUL:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.mul(*operands)
		elif self.operator == self.Operator.MOD:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.urem(*operands)
		elif self.operator == self.Operator.FLOORDIV:
			operands = [_operand.compile(builder, loop_vars) for _operand in self.operands]
			return builder.udiv(*operands)
		else:
			raise ValueError(f"Unsupported operator: {self.operator}")
	'''
	
	def evaluate(self, args):
		if self.operator == self.Operator.ADD:
			x, y = self.operands
			return x.evaluate(args) + y.evaluate(args)
		elif self.operator == self.Operator.SUB:
			x, y = self.operands
			return x.evaluate(args) - y.evaluate(args)
		elif self.operator == self.Operator.MUL:
			x, y = self.operands
			return x.evaluate(args) * y.evaluate(args)
		elif self.operator == self.Operator.ARG:
			n = self.operands
			return args[n]
		elif self.operator == self.Operator.INT:
			n = self.operands
			return n
		else:
			raise NotImplementedError(f"SymbolicInt(operator={self.operator.name}, operands={self.operands}).evaluate")
	
	def _has_for(self):
		if self.operator == self.Operator.FOR:
			return True
		else:
			return super()._has_for()


class SymbolicList(SymbolicExpression):
	_item_type = None
	
	@classproperty
	@cached
	def _item_size(cls):
		if cls._item_type is None:
			return 0
		elif cls._item_type in {SymbolicInt, SymbolicBool}:
			return 1
		elif cls._item_type in {SymbolicExpression, SymbolicList, SymbolicArray, SymbolicTable}:
			raise TypeError
		#else:
		#	symargs, n = build_symbolic_args(cls._item_type.__init__, cls._item_type, None, {})
		#	return n
		else:
			raise NotImplementedError("cls._item_type == " + repr(cls._item_type))
	
	def __class_getitem__(cls, item_type):
		if item_type == None:
			return SymbolicList
		elif item_type in {bool, SymbolicBool}:
			item_type = SymbolicBool
		elif item_type in {int, SymbolicInt}:
			item_type = SymbolicInt
		else:
			raise NotImplementedError("item_type == " + repr(item_type))
		
		return type(f'SymbolicList[{item_type.__name__}]', (SymbolicList,), {'_item_type':item_type})
	
	class Operator(Enum):
		LIST = 'list'
		ARG = 'list_arg'
		FOR = 'list_for'
		APPEND = 'append'
		CHAIN = 'chain'
		PRODUCT = 'product'
	
	#@classmethod
	#def Array(cls, value, sizes, types):
	#	v = list(value)
	#	return cls(v)
	
	@classmethod
	def _const(cls, value):
		if isinstance(value, SymbolicList):
			raise ValueError
		
		value = list(value)
		if not value:
			return cls(cls.Operator.LIST, (value, len(value)))
		else:
			etype = type(value[0])
			
			if etype in {int, SymbolicInt}:
				etype = SymbolicInt
			elif etype in {bool, SymbolicBool}:
				etype = SymbolicBool
			else:
				raise NotImplementedError(f"Unsupported list item type: {etype.__name__}.")
			
			return SymbolicList[etype](cls.Operator.LIST, (value, len(value)))
	
	@classmethod
	def _arg(cls, number, length):
		return cls(cls.Operator.ARG, (number, length))
	
	@classmethod
	def _for(cls, loop_id, name, value):
		if not isinstance(value, cls) and value is not Ellipsis:
			value = cls(value)
			assert hasattr(value, 'operator') and hasattr(value, 'operands')
		return cls(cls.Operator.FOR, (loop_id, name, value))
	
	@classmethod
	def _chain(cls, *values):
		return cls(cls.Operator.CHAIN, tuple(SymbolicList(_value) for _value in values))
	
	@classmethod
	def _product(cls, *values):
		return cls(cls.Operator.PRODUCT, tuple(SymbolicList(_value) for _value in values))
	
	__hash__ = None # mutable object
	
	def _print(self, level=0):
		if self.operator == SymbolicList.Operator.LIST:
			value, length = self.operands
			
			yield level, str(self.operator)
			
			yield level + 1, "["
			for v in value:
				if hasattr(v, '_print'):
					yield from v._print(level + 2)
				else:
					yield level + 2, str(v)
			yield level + 1, "]"
			
			if hasattr(length, '_print'):
				yield from length._print(level + 1)
			else:
				yield level + 1, str(length)
		
		else:
			yield from super()._print()
	
	def _hash(self):
		if not hasattr(self, 'operator') or not hasattr(self, 'operands'): # Unfinished object construction, probably due to exception inside constructor.
			return hash('394834363')
		
		if self.operator == SymbolicList.Operator.LIST:
			value, length = self.operands
			return hash(tuple(value + [length, self.operator]))
		else:
			return super()._hash()
	
	def __len__(self):
		return self._len() // self._item_size()
	
	def _len(self):
		if self.operator == self.Operator.LIST:
			return self.operands[1]
		elif self.operator == self.Operator.ARG:
			return self.operands[1]
		elif self.operator == self.Operator.FOR:
			return SymbolicInt._len(self.__class__(self))
		elif self.operator == self.Operator.CHAIN:
			one, two = self.operands
			return one._len() + two._len()
		elif self.operator == self.Operator.PRODUCT:
			one, two = self.operands
			return one._len() * two._len()
		else:
			raise NotImplementedError
	
	def _get_raw_item(self, index):
		if index < 0:
			index -= self._len()
		
		if self.operator == self.Operator.ARG:
			return SymbolicInt._item(self, index)
		elif self.operator == self.Operator.FOR:
			return SymbolicInt._item(self, index)
		elif self.operator == self.Operator.CHAIN:
			one, two = self.operands
			if index < one._len():
				return one._get_raw_item(index)
			else:
				return two._get_raw_item(index - one._len())
		elif isinstance(index, SymbolicInt):
			return SymbolicInt._item(self, index)
		elif self.operator == self.Operator.LIST:
			return self.operands[0][index]
		else:
			raise NotImplementedError
	
	def __getitem__(self, index):
		assert hasattr(self, 'operator') and hasattr(self, 'operands')
		
		if self._item_type is None:
			raise SpecialIndexError("Empty sequence.")
		elif self._item_type in {int, SymbolicInt}:
			return self._get_raw_item(index)
		elif self._item_type in {bool, SymbolicBool}:
			return self._get_raw_item(index) != 0
		elif self._item_type in {SymbolicExpression, SymbolicList, SymbolicArray, SymbolicTable}:
			raise SpecialTypeError
		else:
			raise NotImplementedError(f"Unsupported list item type: {self._item_type.__name__}.")
			#symargs, n = build_symbolic_args(cls._item_type.__init__, cls._item_type, None, {})
			#return n
	
	'''
	def __replace_arg(self, tree, number, index):
		if tree == SymbolicInt.Operator.ARG:
			if tree.operand == number:
				return SymbolicInt._item(myself, index)
			else:
				return tree
		elif tree == SymbolicList.Operator.ARG:
			if tree.operand == number:
				raise ValueError
			else:
				return tree
		elif isinstance(tree, SymbolicExpression):
			operands = []
			for operand in tree.operands:
				operands.append(self.__replace_args(operand, number, index))
			return tree.__class__(tree.operator, tree.operands)
		else:
			return tree
	'''
	
	def append(self, element):
		one = self.__class__(self)
		two = self.__class__([element])
		#operands = (self.__class__(self), element)
		new = one + two
		self.operator = new.operator
		self.operands = new.operands
	
	def extend(self, sequence):
		operands = self.__class__(self), self.__class__(sequence)
		self.operator = self.Operator.CHAIN
		self.operands = operands
	
	def __add__(self, other):
		self_item_type = self._item_type
		try:
			other_item_type = other._item_type
		except AttributeError:
			other = self.__class__(other)
			other_item_type = other._item_type
		
		if self_item_type is not None and other_item_type is not None and self_item_type != other_item_type:
			raise SpecialTypeError
		
		item_type = self_item_type or other_item_type
		if item_type == self_item_type:
			return self.__class__(self.Operator.CHAIN, (self.__class__(self), other.__class__(other)))
		else:
			return SymbolicList[item_type](self.Operator.CHAIN, (self.__class__(self), other.__class__(other)))
	
	def __iter__(self):
		l = self._len()
		for n in range(l):
			yield self[n]
	
	def _has_for(self):
		if self.operator == self.Operator.FOR:
			return True
		else:
			return super()._has_for()
	
	def __bool__(self):
		cmp = Comparator(self._len() == 0)
		try:
			return boolean_tests[cmp]
		except KeyError:
			raise BooleanTest(cmp)


class SymbolicFunction:
	def __init__(self, fname=None):
		self.fname = fname
	
	def __set_name__(self, cls, sname):
		if self.fname is None:
			self.fname = sname
		self.sname = sname
		self.qualname = cls.__qualname__ + self.fname
	
	def __get__(self, obj, cls=None):
		try:
			return self.call_me
		
		except AttributeError:
			if cls is None:
				cls = type(obj)
			
			annotations = getattr(cls.mro()[1], self.sname).__annotations__
			try:
				return_cls = __annotations__['return']
			except KeyError:
				return_cls = cls
			
			calltypes = []
			for varname, vartype in return_cls.__init__.__annotations__:
				calltype = SymbolicInt # TODO
				calltypes.append(calltype)
			
			def call_me(*args):
				callvars = []
				for calltype in calltypes:
					callvars.append(calltype._call(self.qualname, varname, args))
				return return_cls(*callvars)
			
			call_me.__name__ = self.fname
			call_me.__qualname__ = self.qualname
			self.call_me = call_me
			return call_me


class SymbolicArray:
	required_sizes = None
	required_types = None
	
	def __class_getitem__(cls, args):
		sizes, types = args
		sizes = tuple(sizes)
		types = tuple(types)
		return type(cls.__qualname__, (cls,), {'required_sizes':sizes, 'required_types':types})
	
	def __init__(self, values, sizes=None, types=None, start=None, stop=None, step=None):
		#print("values:", values)
		self.values = SymbolicList(values)
		
		assert isinstance(self.values, SymbolicExpression)
		assert isinstance(self.values, SymbolicList)
		assert hasattr(self.values, 'operator') and hasattr(self.values, 'operands')
		
		if sizes is not None:
			self.sizes = sizes
		else:
			self.sizes = self.required_sizes
		
		if types is not None:
			self.types = types
		else:
			self.types = self.required_types
		
		self.start = start
		self.stop = stop
		self.step = step
	
	def __len__(self):
		return self.sizes[0]
	
	def __getitem__(self, index):
		assert isinstance(self.values, SymbolicList)
		assert hasattr(self.values, 'operator') and hasattr(self.values, 'operands')
		
		if len(self.types) == 1:
			if not isinstance(index, SymbolicInt) and index >= self.sizes[-1]:
				raise IndexError(f"Index {index} out of range ({self.sizes[-1]}).")
			#print(self.types[-1], self.values, index)
			return self.types[-1](self.values[index])
		raise NotImplementedError
	
	def __iter__(self):
		if len(self.types) == 1:
			v = []
			for n in range(RealIterate(len(self))):
				#yield self.types[-1](self.values[n])
				v.append(self.types[-1](self.values[n]))
			#print("yield from", v)
			return iter(v)
		else:
			raise NotImplementedError
	
	#def _print(self, level):
	#	yield level, "Array"
	#	yield from self.values._print(level + 1)
	
	#def __str__(self):
	#	return " ".join(_b for (_a, _b) in self._print())
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + repr(self.values) + ')'
	
	def __eq__(self, other):
		raise NotImplementedError
	
	def _hash(self):
		raise NotImplementedError


class RealIterate:
	def __init__(self, n):
		self.n = n
	
	def __index__(self):
		return self.n


class SymbolicTable:
	required_key_sizes = None
	required_value_sizes = None
	required_types = None
	
	def __class_getitem__(cls, args):
		key_sizes, value_sizes, types = args
		key_sizes = tuple(key_sizes)
		value_sizes = tuple(value_sizes)
		types = tuple(types)
		return type(cls.__qualname__, (cls,), {'required_key_sizes':key_sizes, 'required_value_sizes':value_sizes, 'required_types':types})
	
	def __init__(self, items, key_sizes=None, value_sizes=None, types=None, start=None, stop=None, Array=None):
		raise NotImplementedError


def symeval(func):
	active_loops.clear()
	
	try:
		result = func()
	
	except (ArithmeticError, SpecialTypeError, SpecialValueError, SpecialIndexError, SpecialKeyError) as error:
		return {frozenset(boolean_tests.items()): error}
	
	except LoopIteration as loop:
		loop_index = loop.args[0]
		loop_dependencies = loop.args[1]
		loop_range = loop.args[2]
		loop_body = loop.args[3]
		return {frozenset(boolean_tests.items()): (loop_index, loop_dependencies, loop_range, loop_body)}
	
	except BooleanTest as test:
		tested = test.args[0]
		
		boolean_tests[tested] = True
		yes_trace = symeval(func)
		
		boolean_tests[tested] = False
		no_trace = symeval(func)
		
		del boolean_tests[tested]
		
		result = dict()
		result.update(yes_trace)
		result.update(no_trace)
		return result
	
	else:
		if result is NotImplemented:
			raise RuntimeError(f"`NotImplemented` returned from {func}.")
		return {frozenset(boolean_tests.items()): result}


def symbolic_context():
	symbolic = True
	
	frame = inspect.currentframe().f_back.f_back
	while frame:
		if frame.f_code.co_name in {'__eq__', 'srange', '_hash', '__hash__', 'product', 'len', 'min', 'max', '__init__', 'build_symbolic_args'}:
			symbolic = False
		frame = frame.f_back
	
	return symbolic


def print_stack():
	frame = inspect.currentframe().f_back.f_back
	n = 0
	print(" " * n, frame.f_code.co_name)
	while frame:
		frame = frame.f_back
		n += 1
		print(" " * n, frame.f_code.co_name)


orig_product = product

def product(*lists):
	yield from orig_product(*lists)


orig_chain = chain

def chain(*lists):
	if symbolic_context() and any(isinstance(_value, SymbolicExpression) for _value in lists):
		return SymbolicList._chain(*lists)
	else:
		return orig_chain(*lists)


orig_len = len

def len(seq):
	if hasattr(seq, '_len'):
		return seq._len()
	else:
		return orig_len(seq)


orig_min = min

def min(*values):
	if symbolic_context() and any(isinstance(_value, SymbolicExpression) for _value in values):
		return SymbolicInt._min(*values)
	else:
		return orig_min(*values)


orig_max = max

def max(*values):
	if symbolic_context() and any(isinstance(_value, SymbolicExpression) for _value in values):
		return SymbolicInt._max(*values)
	else:
		return orig_max(*values)


def _different(a, b):
	if isinstance(a, SymbolicExpression) and isinstance(b, SymbolicExpression):
		return Comparator(a) != Comparator(b)
	elif not isinstance(a, SymbolicExpression) and not isinstance(b, SymbolicExpression):
		return a != b
	else:
		return True


orig_range = range

def range(length):
	if symbolic_context():
		return srange(length)
	else:
		print_stack()
		return orig_range(length)


def srange(length):
	real_iterate = isinstance(length, RealIterate)
	
	frame = inspect.currentframe().f_back
	if not real_iterate:
		while frame.f_code.co_name in {'<genexpr>', '__iter__', 'sproduct', '_const', '__init__', 'build_symbolic_args'} or '<lambda>' in frame.f_code.co_name:
			frame = frame.f_back
	
	length = SymbolicInt(length)
	
	ls = frame.f_lineno
	n = SymbolicInt._for(ls, '.', 0)
	
	if n < length:
		loop_dependencies = frozenset(active_loops)
		active_loops.add(ls)
		
		loop_initial = {}
		loop_vars = {}
		pythonapi.PyFrame_FastToLocals(py_object(frame), c_int(0))
		
		for name, value in frame.f_locals.items():
			if isinstance(value, type|Generator|SymbolicList.Operator|SymbolicArray|NoneType|FunctionType):
				pass
			
			elif isinstance(value, int|bool|SymbolicInt):
				loop_initial[name] = SymbolicInt._for(ls, name, value) # initial value
				loop_vars[name] = SymbolicInt._for(ls, name, value) # varying value
			
			elif isinstance(value, tuple|list|SymbolicList):
				if not value:
					loop_initial[name] = SymbolicList._for(ls, name, value) # initial value
					loop_vars[name] = SymbolicList._for(ls, name, value) # varying value
				else:
					etype = type(value[0])
					
					loop_initial[name] = SymbolicList[etype]._for(ls, name, value) # initial value
					loop_vars[name] = SymbolicList[etype]._for(ls, name, value) # varying value
			
			else:
				for argname, argval in zip(value.__init__.__annotations__.keys(), value.__getnewargs__()):
					if isinstance(argval, SymbolicArray): continue
					loop_initial[name + '.' + argname] = argval._for(ls, name, argval) # initial value
					loop_vars[name + '.' + argname] = argval._for(ls, name, argval) # varying value
		
		frame.f_locals.update(loop_vars)
		pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0))
		
		yield n
		
		loop_result = {}
		pythonapi.PyFrame_FastToLocals(py_object(frame), c_int(0))

		for name, value in frame.f_locals.items():
			#print("var", name, value)
			if not isinstance(value, type|Generator) and ((name not in loop_initial) or _different(value, loop_initial[name])):
				loop_result[name] = value # varying value after iteration
		
		raise LoopIteration(ls, loop_dependencies, n < length, loop_result)
	else:
		loop_final = {}
		pythonapi.PyFrame_FastToLocals(py_object(frame), c_int(0))
		for name, value in frame.f_locals.items():
			if isinstance(value, type|Generator|SymbolicList.Operator|SymbolicArray|NoneType|FunctionType):
				pass
			elif isinstance(value, int|bool|SymbolicInt):
				loop_final[name] = SymbolicInt._for(ls, name, ...) # final value
			elif isinstance(value, tuple|list|SymbolicList):
				#print("srange list", name, type(value), value)
				if not value:
					loop_final[name] = SymbolicList._for(ls, name, ...) # final value
				else:
					etype = type(value[0])
					loop_final[name] = SymbolicList[etype]._for(ls, name, ...) # final value
			else:
				for argname, argval in zip(value.__init__.__annotations__.keys(), value.__getnewargs__()):
					if isinstance(argval, SymbolicArray): continue
					loop_final[name + '.' + argname] = argval._for(ls, name, ...) # final value
		frame.f_locals.update(loop_final)
		pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0))
		active_loops.discard(ls)
		
		# Yield some actual values to unpack a sequence.
		instr = [_instr for _instr in get_instructions(frame.f_code) if _instr.offset == frame.f_lasti].pop()
		if instr.opname == 'UNPACK_SEQUENCE':
			yield from orig_range(instr.argval)


def optimize_conditions(sv):
	if len(sv) <= 1:
		return sv
	
	ranking = Counter()
	for kk, vv in sv.items():
		for k, b in kk:
			ranking[k] += 1
	winners = frozenset(_k for _k, _v in ranking.items() if _v == len(sv))
	if not winners:
		return sv
	
	del ranking
	factorized = defaultdict(dict)
	for kk, vv in sv.items():
		fk = set()
		nk = set()
		for k, b in kk:
			if k in winners:
				fk.add((k, b))
			else:
				nk.add((k, b))
		factorized[frozenset(fk)][frozenset(nk)] = vv
	del winners
	return {_kk: optimize_conditions(_vv) for _kk, _vv in factorized.items()}


def build_symbolic_args(fn, selfcls, scalar, replace, n=0):
	args = []
	
	for m, a in enumerate(inspect.getfullargspec(fn).args):		
		t = None
		try:
			t = fn.__annotations__[a]
		except AttributeError:
			raise TypeError(f"Argument type `{selfcls.__name__ + '.' if selfcls else ''}{fn.__name__}` does not have type annotations.")
		except KeyError:
			if selfcls:
				t = selfcls # Arguments of methods with missing annotations are assumed to be self class.
			else:
				raise TypeError(f"Missing type annotation: function `{selfcls.__name__ + '.' if selfcls else ''}{fn.__name__}` argument `{a}` at position {m}.")
		
		if t == Self:
			if selfcls:
				t = selfcls
			else:
				raise TypeError("`Self` annotation on a non-method.")
		
		elif t == FieldType:
			if scalar:
				t = scalar
			else:
				raise TypeError("`FieldType` annotation on a method of type that is not parametrized relative to a field.")
		
		elif isinstance(t, ArrayType):
			sizes = []
			for size in t.sizes:
				if isinstance(size, int):
					pass
				elif size == 'field_power':
					size = scalar.field_power
				else:
					raise NotImplementedError
				sizes.append(size)
			
			types = []
			for type_ in t.types:
				if type_ == Self:
					if selfcls:
						type_ = selfcls
					else:
						raise TypeError("`Self` annotation on a non-method.")
				elif type_ == FieldType:
					if scalar:
						type_ = scalar
					else:
						raise TypeError("`FieldType` annotation on a method of type that is not parametrized relative to a field.")
				
				if replace:
					try:
						type_ = replace[type_]
					except KeyError:
						pass
				
				types.append(type_)
			
			t = SymbolicArray[sizes, types]
		
		elif isinstance(t, TableType):
			key_sizes = []
			for size in t.key_sizes:
				if isinstance(size, int):
					pass
				elif size == 'field_power':
					size = scalar.field_power
				else:
					raise NotImplementedError
				key_sizes.append(size)
			
			value_sizes = []
			for size in t.value_sizes:
				if isinstance(size, int):
					pass
				elif size == 'field_power':
					size = scalar.field_power
				else:
					raise NotImplementedError
				value_sizes.append(size)
			
			types = []
			for type_ in t.types:
				if type_ == Self:
					if selfcls:
						type_ = selfcls
					else:
						raise TypeError("`Self` annotation on a non-method.")
				elif type_ == FieldType:
					if scalar:
						type_ = scalar
					else:
						raise TypeError("`FieldType` annotation on a method of type that is not parametrized relative to a field.")
				
				if replace:
					try:
						type_ = replace[type_]
					except KeyError:
						pass
				
				types.append(type_)
			
			t = SymbolicTable[key_sizes, value_sizes, types]
		
		if replace:
			try:
				t = replace[t]
			except KeyError:
				pass
		
		if m == 0 and fn.__name__ == '__init__': continue # ignore `__init__` first argument
		
		if t == int or t == bool:
			args.append((lambda arg: lambda: arg)(SymbolicInt._arg(n))) # bool argument is also an int
			n += 1
		elif t == list:
			length = SymbolicInt._arg(n + 1)
			args.append((lambda arg: lambda: arg)(SymbolicList._arg(n, length)))
			n += 2
		elif hasattr(t, '__args__') and t.__name__ == 'list':
			length = SymbolicInt._arg(n + 1)
			etype = t.__args__[0]
			args.append((lambda arg: lambda: arg)(SymbolicList[etype]._arg(n, length)))
			n += 2
		elif isinstance(t, type) and issubclass(t, SymbolicArray):
			length = reduce(__mul__, t.required_sizes)
			args.append((lambda arg: lambda: arg)(t(SymbolicList._arg(n, length), t.required_sizes, t.required_types)))
			n += 1
		elif isinstance(t, type) and issubclass(t, SymbolicTable):
			raise NotImplementedError
		elif hasattr(t, '__args__') and len(t.__args__) == 1 and t.__name__ in {Iterable.__name__, Sequence.__name__}:
			itemarg = t.__args__[0]
			
			if itemarg == Self:
				if selfcls:
					itemarg = selfcls
				else:
					raise TypeError("`Self` annotation on a non-method.")
			
			if itemarg == FieldType:
				if scalar:
					itemarg = scalar
				else:
					raise TypeError("`FieldType` annotation on a method of type that is not parametrized relative to a field.")
			
			if replace:
				try:
					itemarg = replace[itemarg]
				except KeyError:
					pass
			
			length = SymbolicInt._arg(n + 1)
			args.append((lambda arg: lambda: arg)(SymbolicList[itemarg]._arg(n, length)))
			n += 2
		elif isinstance(t, type):
			subargs, n_after = build_symbolic_args(t.__init__, t, scalar, replace, n)
			args.append((lambda t, subargs: lambda: t(*subargs()))(t, subargs))
			n = n_after
		else:
			raise NotImplementedError(f"type: {t}")
	
	return (lambda: [_arg() for _arg in args]), n


def trace(fn, selfcls=None, scalar=None, replace=None):
	boolean_tests.clear()
	
	sym_args, n = build_symbolic_args(fn, selfcls, scalar, replace)
	
	#globals_ = {'fn':fn, 'sym_args':sym_args}
	#globals_['__debug__'] = False
	#globals_['range'] = srange
	#globals_['product'] = sproduct
	#globals_['chain'] = schain
	#globals_['len'] = slen
	
	#locals_ = {}
	
	#fn = fn.__class__(fn.__code__, globals_, fn.__name__, None, fn.__closure__)
	closure = lambda: fn(*sym_args())
	
	sv = symeval(closure)
	
	return sv


def print_symeval(sv):
	for kk, vv in sv.items():
		for k, b in kk:
			print("+" if b else "-", " ".join(_b for (_a, _b) in k.expression._print()))
		if isinstance(vv, Exception):
			print(" raise", repr(vv))
		elif isinstance(vv, tuple):
			loop_id, deps, limit, result = vv
			print(f" while({limit})", f"# {loop_id}, {sorted(deps)}")
			for name, value in result.items():
				print(" ", name, "=", repr(value))
		else:
			print(" return", repr(vv))
		print()


def exec_symeval(sv, args):
	for kk, vv in sv.items():
		for k, b in kk:
			if isinstance(k.expression, SymbolicExpression):
				if k.expression.evaluate(args) != b:
					break
			else:
				if bool(k.expression) != b:
					break
		else:
			if isinstance(vv, Exception):
				if isinstance(vv, SymbolicExpression):
					raise vv.evaluate(args)
				else:
					raise vv
			elif isinstance(vv, tuple):
				loop_id, deps, limit, result = vv
				#print(f" while({limit})", f"# {loop_id}, {sorted(deps)}")
				#for name, value in result.items():
				#	print(" ", name, "=", repr(value))
				raise NotImplementedError
			else:
				if isinstance(vv, SymbolicExpression):
					return vv.evaluate(args)
				else:
					return vv


if __name__ == '__main__':
	from aes import Rijndael
	from operations import Linear, Quadratic
	import sys
	
	sys.setrecursionlimit(30)
	
	import operations
	operations.product = product
	operations.chain = chain
	operations.range = range
	
	def t0():
		return 3
	
	def t1():
		return 3 + 5
	
	def t2():
		a = 1
		b = 2
		return a + b
	
	def t3(x:int):
		return x * 7
	
	def t4(x:int):
		x += 1
		x *= 2
		return x
	
	def t5(x:int):
		if x > 5:
			return x + 1
		else:
			return x - 1
	
	def t6(x:int):
		#print(range)
		y = 0
		for i in range(x):
			y += 1
		return y
	
	def t6a():
		return t6(4)
	
	def t7(x:int):
		y = 0
		for i in range(x):
			if i % 2:
				y += 1
		return y
	
	def t7(x:int):
		y = 0
		for a in range(x):
			y += a
			for b in range(a):
				y += b
		for c in range(x):
			y += c
		return y
	
	def t8(x:int):
		y = 0
		if x & 1:
			for a in range(x):
				y += a
				if x & 2:
					for b in range(a):
						y += b
		if x & 4:
			for c in range(x):
				y += c
		return y
	
	def t9(x:list[int]):
		z = 0
		for y in x:
			z += y
		return z
	
	class T:
		def __init__(self, value:int):
			self.value = value
		
		def add(self, other):
			return self.__class__(self.value + other.value)
		
		def inc(self, value:int):
			return self.__class__(self.value + value)
		
		def val(self):
			return self.value
		
		def __repr__(self):
			return self.__class__.__name__ + '(' + repr(self.value) + ')'
	
	class K:
		def __init__(self, value:bool):
			self.value = value
		
		def and_(self, other):
			return self.__class__(self.value and other.value)
		
		def or_(self, other):
			return self.__class__(self.value or other.value)
		
		def ior(self, value:bool):
			return self.__class__(self.value or value)
		
		def __repr__(self):
			return self.__class__.__name__ + '(' + repr(self.value) + ')'
	
	class L:
		def __init__(self, value:K):
			assert hasattr(value, 'value'), repr(value)
			self.k = value
		
		def and_(self, other):
			return self.__class__(K(self.k.value & other.k.value))
		
		def or_(self, other):
			return self.__class__(K(self.k.value | other.k.value))
		
		def ior(self, value:K):
			return self.__class__(K(self.k.value | value.value))
		
		def __repr__(self):
			return self.__class__.__name__ + '(' + repr(self.k) + ')'
	
	def f_single():
		r = 0
		for n in range(10):
			r += n
		return r
	
	def f_serial():
		r = 0
		for n in range(10):
			r += n
		for m in range(10):
			r += m
		return r
	
	def f_chain():
		r = 0
		for n in chain(range(10), range(10)):
			r += n
		return r
	
	def f_nested():
		r = 0
		for n in range(10):
			for m in range(10):
				r += n * m
		return r
	
	def f_product():
		r = 0
		for n, m in product(range(10), range(10)):
			#print("f_product:", n, "::", m)
			r += n * m
		return r
	
	def f_zip1():
		r = 0
		for n, m in zip(range(10), range(10)):
			r += n * m
		return r
	
	def f_zip2():
		r = 0
		for n, m in zip(range(10), range(19)):
			r += n * m
		return r
	
	def f_zip3():
		r = 0
		for n, m in zip(range(19), range(10)):
			r += n * m
		return r
	
	def f_zip_longest1():
		r = 0
		for n, m in zip_longest(range(10), range(10)):
			if n is not None and m is not None:
				r += n * m
		return r
	
	def f_zip_longest2():
		r = 0
		for n, m in zip_longest(range(10), range(19)):
			if n is not None and m is not None:
				r += n * m
		return r
	
	def f_zip_longest3():
		r = 0
		for n, m in zip_longest(range(19), range(10)):
			if n is not None and m is not None:
				r += n * m
		return r
	
	def f_multi():
		r = 0
		
		for n in range(10):
			r += n
		
		for n in range(10):
			for m in range(10):
				r += n * m
			for o in range(10):
				r += n * o
		
		for n in range(10):
			for m in range(10):
				for o in range(10):
					r += n * m * o
		
		return r
	
	def f_unpack1():
		l = []
		for n in range(3):
			l.append(n)
		#print("l =", l._item_type, l)
		a, b, c = l
		return a + b + c
	
	def f_unpack2(l:list[int]):
		a, b, c = l
		return a + b + c
	
	def f_unpack3():
		a, b, c = [1, 2, 3]
		return a + b + c
	
	def mul_everything(s):
		r = 1
		for x in s:
			r *= x
		return r
	
	def l0():
		return mul_everything(x + 1 for x in range(3))
	
	def l1():
		return Rijndael.sum(Rijndael(_x) for _x in range(10))
	
	def l2():
		l = []
		for n in range(10):
			l.append(n)
		return l
	
	def l3(k:list):
		b = True
		for n in k:
			if n % 2:
				b = not b
		return b
	
	def l4():
		l = [m + n for m, n in zip(range(10), range(10))]
		return l
	
	'''
	st0 = trace(t0)
	print_symeval(st0)
	assert t0() == exec_symeval(st0, ())
	
	st1 = trace(t1)
	print_symeval(st1)
	assert t1() == exec_symeval(st1, ())
	
	st2 = trace(t2)
	print_symeval(st2)
	assert t2() == exec_symeval(st2, ())
	
	st3 = trace(t3)
	print_symeval(st3)
	assert t3(1) == exec_symeval(st3, (1,))
	
	st4 = trace(t4)
	print_symeval(st4)
	assert t4(1) == exec_symeval(st4, (1,))
	
	st5 = trace(t5)
	print_symeval(st5)
	assert t5(5) == exec_symeval(st5, (5,))
	'''
	
	#print(l4)
	#sf_zip1 = trace(l4)
	#print(print_symeval(sf_zip1))
	#quit()
	#print(t6(1))

	#assert t6(1) == exec_symeval(st6, (1,))
	
	'''
	for fn in [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9]:
		print(fn.__qualname__)
		print_symeval(trace(fn))
	'''
	
	for fn in [f_single, f_serial, f_chain, f_nested, f_multi, f_unpack1, f_unpack2, f_unpack3, f_zip1, f_zip2, f_zip3, f_zip_longest1, f_zip_longest2, f_zip_longest3, f_product]:
		print(fn.__qualname__)
		print_symeval(trace(fn))
	
	'''
	for fn in [l0, l1, l2, l3, l4]:
		print(fn.__qualname__)
		print_symeval(trace(fn))
	
	for fn in [T.add, T.inc, T.val]:
		print(fn.__qualname__)
		print_symeval(trace(fn, T))
	
	for fn in [K.and_, K.or_, K.ior]:
		print(fn.__qualname__)
		print_symeval(trace(fn, K))
	
	for fn in [L.and_, L.or_, L.ior]:
		print(fn.__qualname__)
		print_symeval(trace(fn, L))
	
	
	class SymbolicRijndael(Rijndael):
		exponent = SymbolicList._const(Rijndael.exponent)
		logarithm = SymbolicList._const(Rijndael.logarithm)
		
		#__add__ = SymbolicFunction()
		#__sub__ = SymbolicFunction()
		#__neg__ = SymbolicFunction()
		#__mul__ = SymbolicFunction()
		#__truediv__ = SymbolicFunction()
		#__pow__ = SymbolicFunction()
	
	for fn in [Rijndael.__add__, Rijndael.__sub__, Rijndael.__neg__, Rijndael.__mul__, Rijndael.__truediv__, Rijndael.__pow__]:
		#print((Rijndael.__name__ + '.') + fn.__name__ + '(' + ', '.join(repr(_arg) for _arg in build_symbolic_args(fn, Rijndael, None, {Rijndael:SymbolicRijndael})[0]()) + ')')
		print(fn.__qualname__)
		print_symeval(trace(fn, Rijndael, None, {Rijndael:SymbolicRijndael}))
	
	class SymbolicLinear(Linear):
		#__add__ = SymbolicFunction()
		#__sub__ = SymbolicFunction()
		#__neg__ = SymbolicFunction()
		#__mul__ = SymbolicFunction()
		#__matmul__ = SymbolicFunction()
		#__call__ = SymbolicFunction()
		pass
	
	for fn in [Linear.__add__]: #, Linear.__sub__, Linear.__neg__]:
		#print((Linear.__name__ + '.') + fn.__name__ + '(' + ', '.join(repr(_arg) for _arg in build_symbolic_args(fn, Linear, Rijndael, {Rijndael:SymbolicRijndael, Linear:SymbolicLinear})[0]()) + ')')
		print(fn.__qualname__)
		print_symeval(trace(fn, Linear, Rijndael, {Rijndael:SymbolicRijndael, Linear:SymbolicLinear}))
	'''


quit()


class SymbolicPointer(SymbolicExpression):
	class Operator(Enum):
		VAR = 'var'
		ARG = 'ptr_arg'
		LIST = 'list'
	
	@classmethod
	def _arg(cls, number):
		return cls(cls.Operator.ARG, number)
	
	@classmethod
	def _var(cls, name):
		return cls(cls.Operator.VAR, name)
	
	@classmethod
	def _list(cls, value):
		return cls(cls.Operator.LIST, list(value))
	
	def __getitem__(self, other):
		other = SymbolicInt(other)
		return SymbolicInt(SymbolicInt.Operator.GETITEM, (self, other))
	
	def serialize(self):
		yield self
	
	def __len__(self):
		if self.operator == self.Operator.LIT:
			return len(self.operands)
		else:
			raise TypeError("Only a literal has defined length.")
	
	def __iter__(self):
		if self.operator == self.Operator.LIT:
			yield from self.operands
		else:
			raise TypeError("Only a literal can be iterated over.")


class FunctionExpression:
	def __init__(self, name):
		self.name = name
	
	def __call__(self, *args):
		print("call", self.name, args)


class SymbolicArray(Array):
	StorageType = SymbolicPointer
	Storage = SymbolicPointer
	cast = SymbolicInt
	
	def __eq__(self, other):
		try:
			return bool(self._Array__storage[self._Array__start:self._Array__stop] == other._Array__storage[other._Array__start:other._Array__stop])
		except AttributeError:
			return NotImplemented
	
	def symbolic_length(self):
		try:
			l = len(self._Array__storage)
		except TypeError:
			l = reduce(__mul__, self._Array__sizes)
		assert l is not None
		return l
	
	def __iter__(self):
		return (self[_n] for _n in srange(self.symbolic_length()))


class SymbolicTable(Table):
	StorageType = SymbolicPointer
	Storage = SymbolicPointer
	cast = SymbolicInt
	
	def __eq__(self, other):
		try:
			return bool(self._Table__storage[self._Table__start:self._Table__stop] == other._Table__storage[other._Table__start:other._Table__stop])
		except AttributeError:
			return NotImplemented




module = ir.Module()

error_func_type = ir.FunctionType(ir.VoidType(), [ir.IntType(8).as_pointer()])
error_func = ir.Function(module, error_func_type, name='error')



def compile_function(name, ll_type, ll_args, algo):
	func_type = ir.FunctionType(ll_type, ll_args)
	func = ir.Function(module, func_type, name=name)
	
	enter = func.append_basic_block()
	r, exit = compile_algo(ll_type, algo, func, enter, {})
	exitbuilder = ir.IRBuilder(exit)
	exitbuilder.ret(r)


def compile_algo(ll_type, algo, func, block, loop_vars):
	if algo is None:
		r, exit = None, block # void
	elif isinstance(algo, int):
		r, exit = ir.Constant(ll_type, algo), block # int constant
	elif isinstance(algo, dict):
		if len(algo) == 1:
			kk, vv = list(algo.items())[0]
			if not kk:
				algo = vv
				r, exit = compile_algo(ll_type, algo, func, block) # empty if
				assert not exit.is_terminated
				return r, exit
		enter = block
		exit = func.append_basic_block()
		r, exit = compile_condition(SymbolicInt.ll_type, algo, func, enter, exit, loop_vars) # if / then / else
	elif isinstance(algo, tuple):
		loop_index = algo[0]
		loop_range = algo[1]
		loop_body = algo[2]
		r, exit = ir.Constant(ll_type, 0), block # FIXME
	elif isinstance(algo, Exception) or algo is NotImplemented:
		r, exit = compile_error(SymbolicInt.ll_type, algo, func, block) # error
	elif hasattr(algo, 'serialize'):
		r, exit = compile_result(SymbolicInt.ll_type, list(algo.serialize())[0], func, block, loop_vars) # object with internal field
	else:
		r, exit = compile_result(SymbolicInt.ll_type, algo, func, block, loop_vars) # expression
	
	assert not exit.is_terminated
	return r, exit


def compile_result(ll_type, algo, func, block, loop_vars):
	builder = ir.IRBuilder(block)
	r = algo.compile(builder, loop_vars)
	assert not block.is_terminated
	return r, block


def compile_error(ll_type, algo, func, block):
	es = repr(algo)
	en = 'error_' + hex(abs(hash(es)))[2:]
	
	try:
		global_string = module.globals[en]
	except KeyError:
		string_type = ir.ArrayType(ir.IntType(8), len(es) + 1) # +1 for the null terminator
		global_string = ir.GlobalVariable(block.function.module, string_type, name=en)
		global_string.initializer = ir.Constant(string_type, bytearray(es.encode('utf-8') + b'\x00'))
		# Set linkage and other attributes if necessary
		global_string.linkage = 'internal'
		global_string.global_constant = True
	
	builder = ir.IRBuilder(block)
	builder.call(error_func, [builder.gep(global_string, [ir.Constant(ir.IntType(16), 0), ir.Constant(ir.IntType(16), 0)])])
	assert not block.is_terminated
	return None, block


def compile_condition(ll_type, algo, func, enter, exit, loop_vars):
	block = enter
	resbuilder = ir.IRBuilder(exit)
	result = resbuilder.phi(ll_type)
	
	prevcond = set() # FIXME
	
	for kk, vv in algo.items():
		builder = ir.IRBuilder(block)
		
		cond = []
		if prevcond != kk:
			prevcond.clear()
			for k, b in kk:
				prevcond.add((k, not b))
				if b:
					cond.append(k.expression.compile(builder, loop_vars))
				else:
					cond.append(builder.not_(k.expression.compile(builder, loop_vars)))
		else:
			prevcond.clear()
			for k, b in kk:
				prevcond.add((k, not b))
		
		if cond:
			cc = reduce(builder.and_, cond)
			hit = func.append_basic_block()
			miss = func.append_basic_block()
			builder.cbranch(cc, hit, miss)
			block = miss
		else:
			hit = block
		
		value, nextblock = compile_algo(ll_type, vv, func, hit)
		assert not nextblock.is_terminated
		if value is not None:
			result.add_incoming(value, nextblock)
			nextbuilder = ir.IRBuilder(nextblock)
			nextbuilder.branch(exit)
		else:
			nextbuilder = ir.IRBuilder(nextblock)
			nextbuilder.ret(ir.Constant(ll_type, 0))
	
	assert not exit.is_terminated
	return result, exit


if __name__ == '__main__':
	from aes import Rijndael
	from operations import Linear
	import sys
	
	sys.setrecursionlimit(5)
	
	#@trace
	#def f0():
	#	pass
	
	'''
	@trace
	def f1(a):
		return a + 1
	
	@trace
	def f2(a, b):
		if a > b:
			return a
		else:
			return b
	
	@trace
	def f3(a, b):
		if a > 0:
			return a
		
		if b > 0:
			return b
		
		return a + b
	
	@trace
	def f4(a, b):
		if a > 0:
			if b > 0:
				return b
		
		return a + b
	
	@trace
	def f5(a, b):
		if a > 0:
			if b > 0:
				return a + b
			raise ValueError("b should be >= 0")
		raise ValueError("a should be >= 0")
	'''
	
	@trace
	def l1():
		l = 0
		for n in range(10):
			l += 1
		return l
	
	@trace
	def l2(a, b):
		l = 0
		for m in range(a):
			for n in range(a):
				l += m * n
		return l
	
	@trace
	def l3(a):
		l = 0
		for m in range(a):
			if m % 2 == 0:
				l -= m
		return l
	
	@trace
	def l4(a, b):
		l = 0
		if b > 0:
			for m in range(a):
				l *= m
		return l
	
	#@trace
	def l5(a, b):
		l = 0
		
		for m in range(a):
			l += m
		
		for n in range(b):
			l += n
		
		return l
	
	@trace
	def l6(a, b):
		l = 0
		
		for m in range(a):
			for n in range(b):
				l += m * n
		
		return l
	
	#@trace
	def l7(a, b, c):
		l = 0
		
		for m in range(a):
			l += m
		
		for n in range(b):
			for o in range(c):
				l += n * o
		
		return l
	
	#l5()
	print("---")
	print()
	l6()
	print("---")
	print()
	#l7()
	print("---")
	
	trace(Rijndael.__add__, Rijndael)
	#trace(Rijndael.__mul__, Rijndael)
	
	#@trace
	#def h(a):
	#	d = 0
	#	for b in srange(a):
	#		if b > 0:
	#			for c in srange(b):
	#				if c > 0:
	#					d += c
	#	return d
	
	#print(module)
	
	
	# Initialize the LLVM binding
	binding.initialize()
	binding.initialize_native_target()
	binding.initialize_native_asmprinter()
	
	# Create a target machine
	target = binding.Target.from_default_triple()
	target_machine = target.create_target_machine()
	
	moduleref = binding.parse_assembly(str(module))
	del module
	
	engine = binding.create_mcjit_compiler(moduleref, target_machine)
	engine.finalize_object()
	
	# Compile the module to object code in memory
	#object_code = target_machine.emit_object(module)
	
	print(engine.get_function_address('f1'))
	
	quit()
	#h()
	
	'''
	closure = symeval(lambda: f(SymbolicPointer._var(0)))
	
	ae1 = SymbolicArray(SymbolicPointer._var(0), [SymbolicInt._var(1)], [Rijndael])
	ae2 = SymbolicArray(SymbolicPointer._var(2), [SymbolicInt._var(3)], [Rijndael])
	
	def g(a):
		d = 0
		for b in range(a):
			d += b
		return d
	
	closure = lambda: g(ae)
	
	closure = lambda: Rijndael.sum(ae)

	closure = lambda: Linear(ae1) + Linear(ae2)
	'''



quit()


# f(f(c, prev), next)




class LoopTransformer(ast.NodeTransformer):
	def __init__(self):
		self.serial = 0
		self.result = []
		self.vars_so_far = set()
		self.calls_so_far = set()
		self.name = None
	
	def __call__(self, block):
		self.serial = 0
		self.result.clear()
		self.vars_so_far.clear()
		self.calls_so_far.clear()
		
		for node in ast.walk(block):
			if isinstance(node, ast.FunctionDef):
				self.vars_so_far.update(_arg.arg for _arg in node.args.args)
				self.name = node.name
				break
		else:
			raise ValueError
		
		self.visit(block)
	
	def visit_Name(self, node):
		#print("name", node.id)
		self.vars_so_far.add(node.id)
		return node
	
	def visit_For(self, node):
		read_vars, write_vars = self.find_used_variables(node)
		
		iter_var = node.target.id
		#print("for", iter_var)
		read_vars.remove(iter_var)
		write_vars.remove(iter_var)
		
		try:
			seq_var = node.iter.id
		except AttributeError:
			pass

		#print(iter_var, read_vars, self.vars_so_far)
		in_vars = [iter_var] + list(read_vars & self.vars_so_far)
		out_vars = list(write_vars)
		
		# Generate the recursive function
		r = self.__class__()
		recursive_func = ast.fix_missing_locations(self.generate_recursive_function(node, in_vars, out_vars))
		r(recursive_func)
		self.result.extend(r.result)
		self.result.append(recursive_func)
		
		replacement = self.generate_replacement_code(node, in_vars, out_vars)
		self.serial += 1
		return ast.fix_missing_locations(replacement)
	
	def generate_recursive_function(self, for_loop, in_vars, out_vars):
		# Create the recursive function definition
		recursive_func_name = f"{self.name}__{self.serial}"
		seq_arg = f"_seq__{self.serial}"
		args = ast.arguments(
			posonlyargs=[],
			args=[
				*[ast.arg(arg=var, annotation=None) for var in in_vars]
			],
			kwonlyargs=[],
			kw_defaults=[],
			defaults=[]
		)

		# Create the function body
		body = [
			*for_loop.body,
			ast.Return(
				value=ast.Tuple(
					elts=[
						*[ast.Name(id=var, ctx=ast.Load()) for var in out_vars]
					],
					ctx=ast.Load()
				)
			)
		]

		return ast.FunctionDef(
			name=recursive_func_name,
			args=args,
			body=body,
			decorator_list=[],
			returns=None
		)
	
	def generate_replacement_code(self, for_loop, in_vars, out_vars):
		#iter_var = for_loop.target.id
		seq_val = ast.unparse(for_loop.iter)
		recursive_func_name = f'{self.name}__{self.serial}'
		seq_arg = f'_seq__{self.serial}'
		cnt_arg = for_loop.target.id
		
		if isinstance(for_loop.iter, ast.Call) and isinstance(for_loop.iter.func, ast.Name) and for_loop.iter.func.id == 'range':
			#print(dir(for_loop.iter))
			repl_fn = 'range(' + ast.unparse(for_loop.iter.args) + ')'
			repl_item = cnt_arg
		else:
			repl_fn = f'range(len({seq_val}))'
			repl_item = f'{seq_val}[{cnt_arg}]'
		
		in_vars = list(in_vars)
		in_vars[0] = repl_item
		
		if out_vars:
			return ast.parse(f'''
for {cnt_arg} in {repl_fn}:
	{", ".join(out_vars)} = {recursive_func_name}({", ".join(in_vars)})
''')
		else:
			return ast.parse(f'''
for {cnt_arg} in {repl_fn}:
	{recursive_func_name}({", ".join(in_vars)})
''')
	
	def find_used_variables(self, block):
		read_vars = set()
		write_vars = set()
		calls = set()
		for node in ast.walk(block):
			if isinstance(node, ast.Name):
				if isinstance(node.ctx, ast.Load):
					read_vars.add(node.id)
				elif isinstance(node.ctx, ast.Store):
					write_vars.add(node.id)
			elif isinstance(node, ast.Call):
				if isinstance(node.func, ast.Name):
					calls.add(node.func.id)
		return read_vars - calls, write_vars - calls


def function_ast(fn):
	source = inspect.getsource(fn)
	lines = source.splitlines()
	if lines:
		# Determine the indentation level from the first line
		first_line = lines[0]
		leading_spaces = len(first_line) - len(first_line.lstrip())
		# Remove the leading spaces from each line
		deindented_lines = [line[leading_spaces:] for line in lines]
		source = '\n'.join(deindented_lines)
	return ast.parse(source)


if __name__ == '__main__':
	from aes import Rijndael
	from operations import Linear
	import sys

	sys.setrecursionlimit(5)
	
	def col(a, b, c, d, e):
		p = 0
		k = zip(a, b)
		for xy in k: # used variables: p; not used: x, y because they were undefined at loop entry
			x = xy[0]
			y = xy[1]
			if x > y:
				p += 1
		
		q = 0
		l = zip(a, c)
		for xy in l: # used variables: x, y, q; the variables x, y have been defined in the previous loop
			x = xy[0]
			y = xy[1]
			if x > y:
				q += 1
		
		r = 0
		s = 0
		m = zip(a, d)
		for xy in m: # used variables: xm, ym, xn, yn, r, s, a, e, n, xyn; not used: zip (a callable)
			xm = xy[0]
			ym = xy[1]
			if xm > ym:
				r += 1
			
			n = zip(a, e)
			for xyn in n:
				xn = xyn[0]
				yn = xyn[1]
				if xn > yn:
					s += 1
		
		return p + q + r + s
	
	s = function_ast(Linear.__matmul__)
	print(ast.unparse(s))
	print()
	
	r = LoopTransformer()
	r(s)
	
	l = {'range':srange}
	for f in r.result:
		f = ast.parse(ast.unparse(f))
		print(ast.unparse(f))
		print()
		p = compile(f, '<string>', 'exec')
		exec(p, l)
		#n = list(l.keys() - {'__builtins__'})[0]
		#print(n)
		#print(l[n]())
	
	l = {'range':srange, '__matmul____0':FunctionExpression('__matmul____0')}
	print(ast.unparse(s))
	print()
	p = compile(ast.unparse(s), '<string>', 'exec')
	exec(p, l)
	
	a = SymbolicInt._var('a')
	c = SymbolicArray(SymbolicPointer._var('c'), [None], [Rijndael])
	d = SymbolicArray(SymbolicPointer._var('d'), [None], [Rijndael])
	
	sys.setrecursionlimit(20)
	
	k = symeval(lambda: l['__matmul__'](Linear(c), Linear(d)))
	for kk, vv in k.items():
		for k, b in kk:
			print("+" if b else "-", " ".join(_b for (_a, _b) in k.expression._print()))
		print(" ", type(vv).__name__ + ":", repr(vv))
		print()




quit()



'''

if True:
	# modified function
	def col(a):
		# code before the loop
		r = 3
		k = 1
		l = 0
		
		# replacement function; takes sequence and used variables; returns iteration variable and used variables
		if seq:
			v, r, k = col__0(a, r, k)
		
		# code after the loop
		k += r
		k += l
		return r + k + l

	# recursive function; takes sequence argument (under special name) and used variables
	def col__0(_seq__0, r, k):
		# special case: return None and used variables if sequence is empty
		if not _seq__0:
			return None, r, k
		
		# recursion
		v, r, k = col_loop(_seq__0[:-1], r, k)
		# initialize iteration variable
		v = _seq__0[-1]
		
		# loop body
		r += 2 * v
		k += 1
		
		# return iteration variable and used variables
		return v, r, k
		
		a = Rijndael(SymbolicInt._var('a'))
		b = Rijndael(SymbolicInt._var('b'))
		
		r = a + b
		for level, line in list(r.serialize())[0]._print():
			print(" " * level, line)
		print()
		
		c = SymbolicArray(SymbolicPointer._var('c'), [None], [Rijndael])
		for level, line in c._Array__storage._print():
			print(" " * level, line)
		print()
		
		#print(c._Array__storage)
		#print(c[0])
		
		boolean_tests.clear()
		k = symeval(lambda: col(c))
		
		for kk, vv in k.items():
			for k, b in kk:
				print("+" if b else "-", " ".join(_b for (_a, _b) in k.expression._print()))
			print(" ", type(vv).__name__ + ":", vv)
			print()
		
		#r = Rijndael.sum(c)
		#print(r)
		#for level, line in list(r.serialize())[0]._Array__storage._print():
		#	print(" " * level, line)
		#print()















'''







quit()


from utils import singleton
from memory import Array, Table
from sys import settrace
from inspect import getsourcelines, getfullargspec, currentframe
from typing import Self, TypeVar
from collections import defaultdict
from ctypes import pythonapi, py_object, c_int
from types import SimpleNamespace
from collections.abc import Generator
from itertools import chain


class Cmd:
	def __init__(self, mnemonic, operands):
		self.mnemonic = mnemonic
		self.operands = list(operands)
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + repr(self.mnemonic) + ', ' + repr(self.operands) + ')'
	
	def __hash__(self):
		return hash((self.mnemonic, tuple(hash(_op) for _op in self.operands)))
	
	def __eq__(self, other):
		try:
			return self.mnemonic == other.mnemonic and self.operands == other.operands
		except AttributeError:
			return NotImplemented
	
	def __bool__(self):
		raise RuntimeError("Term instances should not be tested for truth value.")
	
	def _print_tree(self, level=0):
		print((" " * level) + self.mnemonic)
		for op in self.operands:
			if isinstance(op, self.__class__):
				op._print_tree(level=level+1)
			else:
				print(" " * level, repr(op))


class Term:
	def __init__(self, mnemonic, operands):
		self.mnemonic = mnemonic
		self.operands = list(operands)
		
		if not all(isinstance(_op, self.__class__ | str | int | type | type(Ellipsis)) for _op in self.operands):
			raise TypeError(f"One of operands is neither Term, str, int, type nor Ellipsis. {[type(_op).__name__ for _op in self.operands]}")
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + repr(self.mnemonic) + ', ' + repr(self.operands) + ')'
	
	def __hash__(self):
		return hash((self.mnemonic, tuple(hash(_op) for _op in self.operands)))
	
	def __eq__(self, other):
		try:
			return self.mnemonic == other.mnemonic and self.operands == other.operands
		except AttributeError:
			return NotImplemented
	
	def __bool__(self):
		raise RuntimeError("Term instances should not be tested for truth value.")
	
	def _print_tree(self, level=0):
		print((" " * level) + self.mnemonic)
		for op in self.operands:
			if isinstance(op, self.__class__):
				op._print_tree(level=level+1)
			else:
				print(" " * level, repr(op))
	
	def _search(self, subterm):
		if self.mnemonic == subterm.mnemonic and len(self.operands) == len(subterm.operands):
			for a, b in zip(self.operands, subterm.operands):
				if b is not Ellipsis and a != b:
					break
			else:
				return True
		
		for op in self.operands:
			try:
				_search = op._search
			except AttributeError:
				continue
			
			if _search(subterm):
				return True
		
		return False


unary_arithmetics = 'neg', 'plus'
binary_arithmetics = 'add', 'sub', 'mul', 'mod', 'pow', 'xor'
binary_comparisons = 'eq', 'ne', 'ge', 'lt', 'gt', 'le'


class BooleanTest(BaseException):
	pass


class LoopVarsModified(BaseException):
	pass


def make_unary_closure(name):
	return lambda one: one.__class__(Term(name, [one.symbolic_value()]))


def make_binary_closure(name):
	return lambda one, two: one.__class__(Term(name, [one.symbolic_value(), one.__class__(two).symbolic_value()]))


def make_reversed_closure(name):
	return lambda one, two: one.__class__(Term(name, [one.__class__(two).symbolic_value(), one.symbolic_value()]))


@singleton
def Arithmetics():
	operations = {}
	
	for name in unary_arithmetics:
		operations[f'__{name}__'] = make_unary_closure(name)
	
	for name in binary_arithmetics:
		operations[f'__{name}__'] = make_binary_closure(name)
		operations[f'__r{name}__'] = make_reversed_closure(name)
	
	return type('Arithmetics', (), operations)


@singleton
def Relations():
	operations = {}
	
	for name in binary_comparisons:
		operations[f'__{name}__'] = make_binary_closure(name)
	
	return type('Arithmetics', (), operations)


class SymbolicInt(Arithmetics, Relations):
	"Scalar value. Symbolic representation of Python `int`."
	
	py_type = int
	
	def __init__(self, value):
		try:
			self.__value = value.__value
		except AttributeError:
			self.__value = value
		
		if not isinstance(self.__value, Term | int):
			raise TypeError(f"Value should be a Term or int, got {type(self.__value).__name__} instead.")
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + repr(self.__value) + ')'
	
	def __eq__(self, other):
		try:
			return self.__class__(Term('eq', [self.symbolic_value(), other.symbolic_value()]))
		except AttributeError:
			return NotImplemented
	
	__hash__ = None
	
	def __bool__(self):
		try:
			result = _tracer.tests[self.__value]
			_tracer.traces.append(Cmd('test', [self.symbolic_value(), result]))
			return result
		except KeyError:
			raise BooleanTest(self.__value)
	
	def symbolic_value(self):
		return self.__value
	
	def serialize(self):
		yield self.symbolic_value()


'''
class SymbolicFunction:
	def __init__(self, value):
		try:
			self.__value = value.__value
		except AttributeError:
			self.__value = value
	
	__hash__ = None
	
	def __call__(self, *args):
		call = Term('call', [self.__pointer, Term('args', args)])
		_tracer.traces.append(call)
		return call
'''


class SymbolicPtr(Relations):
	"Array value. Symbolic representation of Python `list`."
	
	py_type = list
	
	def __init__(self, value):
		try:
			self.__value = value.__value
			self.__length = value.__length
		except AttributeError:
			if isinstance(value, list):
				self.__value = Term('list', ['?'])
				self.__length = len(value)
			else:
				raise ValueError
		
		if not isinstance(self.__value, Term):
			raise TypeError(f"Value should be a Term, got {type(self.__value).__name__} instead.")
	
	__hash__ = None
	
	def __repr__(self):
		return "SymbolicPtr(" + repr(self.__value) + ")"
	
	def __len__(self):
		raise TypeError
	
	def __getitem__(self, index):
		if hasattr(index, 'start') and hasattr(index, 'stop'):
			raise NotImplementedError
		else:
			return SymbolicInt(Term('getitem', [self.symbolic_value(), SymbolicInt(index).symbolic_value()]))
	
	def __setitem__(self, index, value):
		_tracer.traces.append(Cmd('setitem', [self.symbolic_value(), SymbolicInt(index).symbolic_value(), value]))
	
	def symbolic_value(self):
		return self.__value
	
	def symbolic_length(self):
		return SymbolicInt(Term('length', [self.__value]))


class SymbolicArray(Array):
	"Single-dimensional array (addressed by ints), whose elements may be scalars or other arrays."
	
	StorageType = SymbolicPtr
	Storage = SymbolicPtr
	cast = SymbolicInt
	
	def __repr__(self):
		return "SymbolicArray(" + repr(self._Array__storage) + ")"
	
	#def make_similar(self, value):
	#	array = SymbolicArray(self)
	#	array._Array__storage = value
	#	return array
	
	#def symbolic_length(self):
	#	return self._Array__storage.symbolic_length()
	
	def serialize(self):
		return self._Array__storage[self.__start:self.__stop]
	
	def __iter__(self):
		for n in symbolic_range(self.symbolic_length()):
			yield self[n]


'''
class SymbolicTable(Table):
	"Multi-dimensional tables (addressed by tuples of ints), whose elements may be tables, arrays or scalars."
	StorageType = SymbolicPtr
	Storage = SymbolicPtr
	cast = SymbolicInt
'''

Scalar = TypeVar('Scalar')


def symbolic_length(obj):
	try:
		return obj.symbolic_length()
	except AttributeError:
		return obj.__len__()


def symbolic_range(limit):
	ln = _tracer.loop_number
	_tracer.traces.append(Cmd('begin', [ln, SymbolicInt(limit).symbolic_value()]))
	
	frame = currentframe().f_back
	vars_orig = dict(frame.f_locals)
	
	vars_before = dict()
	for v in vars_orig.keys():
		if (v, ln) in _tracer.unmodified:
			pass
		elif isinstance(vars_orig[v], int | SymbolicInt):
			vars_before[v] = SymbolicInt(Term('for', [int, v, ln]))
		elif isinstance(vars_orig[v], list | SymbolicPtr):
			vars_before[v] = SymbolicPtr(Term('for', [list, v, ln]))
		elif isinstance(vars_orig[v], Generator):
			#vars_before[v] = vars_orig[v]
			pass
		else:
			raise NotImplementedError(type(vars_orig[v]))
	frame.f_locals.update(vars_before)
	pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0)) # FIXME: not needed in python >= 3.13
	
	yield SymbolicInt(Term('for', [int, '_', ln]))
	
	unmodified = set()
	frame = currentframe().f_back
	vars_after = dict(frame.f_locals)
	for v in vars_after.keys():
		if (v, ln) in _tracer.unmodified:
			pass
		elif v not in vars_before:
			try:
				tt = type(vars_after[v]).py_type
			except AttributeError:
				tt = type(vars_after[v])
			term = SymbolicInt(Term('for', [tt, v, ln]))
			_tracer.traces.append(Cmd('iter', [ln, term, 0, vars_after[v]]))
			vars_after[v] = term
		elif vars_before[v] is vars_after[v]: #or get_result(vars_before[v]) is get_result(vars_after[v]):
			unmodified.add((v, ln))
			#vars_after[v] = vars_before[v]
		else:
			_tracer.traces.append(Cmd('iter', [ln, vars_before[v], vars_orig[v], vars_after[v]]))
			vars_after[v] = vars_before[v]
	
	if unmodified:
		_tracer.unmodified.update(unmodified)
		raise LoopVarsModified
	
	frame.f_locals.update(vars_after)
	pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0)) # FIXME: not needed in python >= 3.13
	
	_tracer.traces.append(Cmd('end', [ln]))


def trace_fn(frame, event, param):
	if event == 'call' and frame.f_code.co_qualname.startswith('Arithmetics.') or frame.f_code.co_qualname in ['symbolic_range', 'symbolic_length']:
		_tracer.inside = False
	elif event == 'call' and frame.f_code.co_qualname == _tracer.fname:
		_tracer.inside = True
	
	if _tracer.inside:
		return trace_do


def trace_do(frame, event, param):
	lineno = frame.f_lineno
	_tracer.branches[_tracer.prev_lineno].add(lineno)
	_tracer.prev_lineno = lineno
	
	_tracer.loop_number = lineno # TODO
	_tracer.inside = True
	
	if event == 'return' and frame.f_code.co_qualname == _tracer.fname:
		_tracer.inside = False
	elif event == 'line':
		if lineno in _tracer.lines and lineno not in _tracer.loops:
			ls, sl = getsourcelines(frame.f_code)
			_tracer.loops.add(lineno)
			#if ls[lineno - sl].strip().startswith('for '):
			#print("loop", frame.f_code.co_qualname, lineno, dict((_name, _value) for (_name, _value) in frame.f_locals.items()))
			#print("::", ls[lineno - sl])
			##	#raise EnterLoop
		else:
			_tracer.lines.add(lineno)
	
	return trace_do


def symeval():
	assert _tracer.traces is None
	
	try:
		_tracer.traces = []
		result = _tracer.fun(*_tracer.fargs)
		traces = _tracer.traces
		_tracer.traces = None
		return {frozenset(_tracer.tests.items()): [traces, result]}
	
	except (IndexError, ArithmeticError, AssertionError) as error:
		traces = _tracer.traces
		_tracer.traces = None
		return {frozenset(_tracer.tests.items()): [traces, error]}
	
	except BooleanTest as test:
		tested = test.args[0]
		
		_tracer.traces = None
		_tracer.unmodified.clear()
		assert test not in _tracer.tests
		
		_tracer.tests[tested] = True
		yes_trace = symeval()
		
		_tracer.tests[tested] = False
		no_trace = symeval()
		
		if tested not in _tracer.tests:
			result = dict()
			result.update({yes_cond : yes_value for (yes_cond, yes_value) in yes_trace.items() if (tested, True) not in yes_cond})
			return result
		
		del _tracer.tests[tested]
		
		tests = frozenset(_tracer.tests.items())
		
		yes_test = frozenset({(tested, True)})
		no_test = frozenset({(tested, False)})
		
		result = dict()
		result.update({yes_cond | yes_test : yes_value for (yes_cond, yes_value) in yes_trace.items()})
		result.update({no_cond | no_test : no_value for (no_cond, no_value) in no_trace.items()})
		return result
	
	except LoopVarsModified:
		for t in list(_tracer.tests.keys()):
			if any(t._search(Term('for', [..., v, ln])) for (v, ln) in _tracer.unmodified):
				#print("del", t)
				del _tracer.tests[t]
		_tracer.traces = None
		return symeval()


def trace(fn, default_type):
	"fn - function to call; cls - self type; scl - scalar type"
	
	global _tracer
	
	try:
		_tracer
	except NameError:
		pass
	else:
		raise RuntimeError("There may be only one tracer running.")
	
	_tracer = SimpleNamespace()
	_tracer.inside = False
	_tracer.lines = set()
	_tracer.loops = set()
	_tracer.branches = defaultdict(set)
	_tracer.prev_lineno = None
	_tracer.loop_number = None
	_tracer.traces = None
	_tracer.unmodified = set()
	_tracer.tests = {}
	#_tracer.loop_entered = set()
	
	fname = fn.__qualname__	
	asp = getfullargspec(fn)
	fargs = []
	for argname in asp.args + ['return']:
		try:
			arg_cls = fn.__annotations__[argname]
		except KeyError:
			arg_cls = default_type
		
		try:
			py_type = arg_cls.py_type
		except AttributeError:
			py_type = arg_cls
		
		if argname != 'return':
			term = Term('arg', [py_type, argname])		
			if py_type == int:
				arg = SymbolicInt(term)
			elif py_type == list:
				arg = SymbolicPtr(term)
			else:
				raise NotImplementedError(py_type.__name__)
			
			if arg_cls != py_type:
				arg = arg_cls(arg)
			
			fargs.append(arg)
		else:
			rettype = arg_cls
	
	_tracer.fname = fname
	_tracer.fargs = fargs
	#_tracer.types = types
	
	#print("rettype", rettype)
	fun = type(fn)(fn.__code__, {'range':symbolic_range, 'len':symbolic_length, 'Array':SymbolicArray, '_tracer':_tracer}, fname)
	_tracer.fun = fun
	#_tracer.fun = lambda *args: rettype(fun(*args))
	
	settrace(trace_fn)
	try:
		trace_result = symeval()
	finally:
		settrace(None)
	
	del _tracer	
	return trace_result


def get_result(x):
	if isinstance(x, int):
		return x
	else:
		return x._SymbolicInt__value


if False and __name__ == '__main__':
	def test_me_1(e):
		k = 0
		l = 0
		
		if e < 2:
			for i in range(e):
				if k > 0:
					k += 1
				else:
					k += 2
				
				if l < 0:
					l += 3
					pass
		
		for j in range(k):
			if k > 1:
				k += 4
			else:
				k += 5
			
			if l < 1:
				l += 6
				pass
		
		r = 0
		for i in range(j):
			r += 10 * i
			for j in range(l + 10):
				r += j
		
		return k * l * r
	
	from aes import Rijndael
	Rijndael.c_backing = c_int
	
	trace_result = trace(Rijndael.__add__, Rijndael, None)
	
	for cond, (tr, result) in trace_result.items():
		for c in sorted(cond, key=repr):
			print("?", c)
		for t in tr:
			print(" :", t)
		
		if isinstance(result, Exception):
			print("!", type(result).__name__, result)
		elif isinstance(result, BaseException):
			raise ValueError
		else:
			if hasattr(result, 'serialize'):
				r = get_result(list(result.serialize())[0])
			else:
				r = result
			
			if hasattr(r, '_print_tree'):
				print("→")
				r._print_tree()
			else:
				print("→", r)
		
		print()


if __name__ == '__main__':
	from aes import Rijndael
	from operations import Linear, Quadratic
	
	class SymbolicRijndael(Rijndael):
		py_type = int
		
		logarithm = SymbolicPtr(Term('const', [list, 'Rijndael.logarithm']))
		exponent = SymbolicPtr(Term('const', [list, 'Rijndael.exponent']))
		
		#@classmethod
		#def symbolic_create(cls, term):
		#	return cls(SymbolicInt(term))
		
		#def symbolic_extract(self):
		#	return get_result(list(self.serialize())[0])
		
		#sum = SymbolicFunction(Term('func', ['*u8,u32→u8', 'Rijndael.sum']))
	
	class SymbolicLinear(Linear):
		py_type = list
		#c_backing = '*u8'
		#c_length = 8
		
		#@classmethod
		#def symbolic_create(cls, term):
		#	return cls(SymbolicArray(SymbolicPtr(term, 8), [None], [SymbolicRijndael]))
		
		#def symbolic_extract(self):
		#	
		#	items = [_item.symbolic_extract() for _item in self.serialize()]
		#	return items
		#	#print(items)
		#	#raise NotImplementedError
		#	#return cls(SymbolicArray(SymbolicPtr(term, 8), [None], [SymbolicRijndael]))
		
		#def __call__(self, x:SymbolicRijndael) -> SymbolicRijndael:
		#	return super()(x)
	
	#trace_result = trace(Linear.__call__, SymbolicLinear, SymbolicRijndael)
	
	def t0():
		a = 1
		return a
	
	def t1(x:int):
		return x + 1
	
	def t2(x:int):
		if x > 0:
			return 1
		else:
			return 2
	
	def t3(x:int):
		j = 1
		for i in range(x):
			j += i
		return j
	
	def t4(x:int, y:int):
		k = 0
		for i in range(x):
			for j in range(i + y):
				k += i * j
		return k
	
	def t5(x:int):
		a = [0] * x
		for i in range(x):
			a[i] = i
		return a
	
	def aaa(x:int, y:int):
		if x > y:
			return x + y
		
		k = 0
		for n in range(y):
			k += x * n
		return k
	
	def bbb(l:list, x:int):
		r = x
		for n in range(len(l)):
			if l[n] > 0:
				r += l[n]
		return r
	
	def ccc(a:list, b:list):
		assert len(a) == len(b)
		c = Array((a[n] + b[n] for n in range(len(a))), [10], [None])
		return c
	
	#f = Rijndael(SymbolicInt(Term('arg', ['u8', 0])))
	#g = Rijndael(SymbolicInt(Term('arg', ['u8', 1])))
	#l = Linear(SymbolicArray(SymbolicPtr(Term('arg', ['*u8', 2]), 8), [None], [Rijndael]))
	#q = Quadratic(SymbolicArray(SymbolicPtr(Term('arg', ['*u8', 2]), 64), [8, None], [Linear, Rijndael]))
	
	#def m(x, y):
	#	return get_result(list((Rijndael(SymbolicInt(x)) * Rijndael(SymbolicInt(y))).serialize())[0])
	#
	#def d(x, y):
	#	return get_result(list((Rijndael(SymbolicInt(x)) / Rijndael(SymbolicInt(y))).serialize())[0])
	#
	#def a(x):
	#	return Rijndael.sum(x)
	#
	#def b(xs, y):
	#	return get_result(list(Linear(SymbolicArray(SymbolicPtr(xs, 8), [None], [Rijndael]))(Rijndael(SymbolicInt(y))).serialize())[0])
	
	
	trace_result = trace(t5, None)
	#trace_result = trace(bbb, None)
	#trace_result = trace(ccc, None)
	#trace_result = trace(SymbolicRijndael.__add__, SymbolicRijndael)
	#trace_result = trace(SymbolicLinear.__add__, SymbolicLinear)
	
	for cond, (tr, result) in trace_result.items():
		for c in sorted(cond, key=repr):
			print("?", c)
		for t in tr:
			print(" :", t)
		
		if isinstance(result, Exception):
			print("!", type(result).__name__, result)
		elif isinstance(result, BaseException):
			raise ValueError
		else:
			print("→", result)
			#if hasattr(result, 'symbolic_extract'):
			#	r = result.symbolic_extract()
			#elif hasattr(result, 'serialize'):
			#	r = get_result(list(result.serialize())[0])
			#else:
			#	r = result
			
			#if hasattr(r, '_print_tree'):
			#	print("→", type(r).__name__)
			#	r._print_tree()
			#else:
			#print("→", type(r), r)
		
		print()
