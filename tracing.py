#!/usr/bin/python3


from utils import *
from enum import Enum

from typing import Generator, Optional, Callable
from types import NoneType
import inspect
from ctypes import pythonapi, py_object, c_int
from memory import Backing, Array, Table
from itertools import chain

#from itertools import chain, product, zip_longest
#import ast
#import inspect
#from functools import reduce
#from operator import __mul__
#from collections import Counter, defaultdict
#from collections.abc import Iterable, Sequence
#from typing import Self, Generator, Iterator, Any
from dis import get_instructions
#from types import FunctionType, NoneType, SimpleNamespace


class BooleanTest(BaseException):
	pass


class LoopIteration(BaseException):
	pass


boolean_tests = dict()
active_loops = dict()


class Comparator:
	def __init__(self, expression:'SymbolicExpression'):
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
			except TypeError: # operands not iterable
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
		if operator.__class__.__name__ == 'Operator' and operands is None:
			raise ValueError("If `operator` is an Operator then `operands` must not be None.")
		
		if operands is None:
			try:
				self.operator = operator.operator
				self.operands = operator.operands
			except AttributeError:
				assert not isinstance(operator, SymbolicExpression)
				const = self._const(operator) # Create symbolic const from Python object.
				assert hasattr(const, 'operator') and hasattr(const, 'operands')
				self.operator = const.operator
				self.operands = const.operands
		else:
			self.operator = operator
			self.operands = operands
		
		assert hasattr(self, 'operator') and hasattr(self, 'operands')
		
		if not isinstance(self.operator, self.Operator):
			raise ValueError(f"`operator` must be {self.Operator}, got {type(operator)}.")
		
		if __debug__:
			"Make sure all operands are hashable."
			
			try:
				ops = iter(self.operands)
			except TypeError:
				hash(self.operands)
			else:
				for operand in ops:
					try:
						hash(operand)
					except TypeError:
						operand._hash()
	
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
				oph = hash(self.operands)
			ops.append(oph)
		
		return hash(tuple(ops))
	
	__hash__ = _hash
	
	def __str__(self):
		return repr(self)
	
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
		if other.__class__.__name__ == 'Operator':
			return NotImplemented
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
	
	@classmethod
	def _arg(cls, func_name:str, var_name:str):
		"Argument of a function."
		if not isinstance(func_name, str):
			raise ValueError
		if not isinstance(var_name, str):
			raise ValueError
		
		return cls(cls.Operator.ARG, (func_name, var_name))
	
	@classmethod
	def _for(cls, loop_id:str, name:Optional[str]):
		"Variable inside a loop."
		if not isinstance(loop_id, str):
			raise ValueError
		if not isinstance(name, str) and name is not None:
			raise ValueError
		
		return cls(cls.Operator.FOR, (loop_id, name))
	
	@classmethod
	def _loop(cls, loop_id:str, name:str):
		"Value that is result of loop evaluation after it has ended."
		if not isinstance(loop_id, str):
			raise ValueError
		if not isinstance(name, str):
			raise ValueError
		
		return cls(cls.Operator.LOOP, (loop_id, name))


class SymbolicBool(SymbolicExpression):
	"Herbrand model of Python computation. Symbolic `bool` value."
	
	class Operator(Enum):
		CONST = 'const'
		FOR = 'for'
		LOOP = 'loop'
		ARG = 'arg'
		WHILE = 'while'
		
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
	def _const(cls, value:Optional[bool]):
		if value is None: value = False
		
		if not isinstance(value, bool):
			raise ValueError("`value` must be bool.")
		
		return cls(cls.Operator.CONST, value)
	
	def _while(self, loop_id):
		return self.__class__(self.Operator.WHILE, (self, loop_id))
	
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
	
	def __str__(self):
		if self.operator == self.Operator.EQ:
			x, y = self.operands
			return str(x) + " == " + str(y)
		elif self.operator == self.Operator.NE:
			x, y = self.operands
			return str(x) + " != " + str(y)
		elif self.operator == self.Operator.GT:
			x, y = self.operands
			return str(x) + " > " + str(y)
		elif self.operator == self.Operator.LT:
			x, y = self.operands
			return str(x) + " < " + str(y)
		elif self.operator == self.Operator.GE:
			x, y = self.operands
			return str(x) + " >= " + str(y)
		elif self.operator == self.Operator.LE:
			x, y = self.operands
			return str(x) + " <= " + str(y)
		elif self.operator == self.Operator.CONST:
			return str(self.operands)
		elif self.operator == self.Operator.WHILE:
			return "for(" + self.operands[1] + " = 0; " + str(self.operands[0]) + "; " + self.operands[1] + "++)"
		else:
			raise NotImplementedError
	
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
		elif self.operator == self.Operator.CONST:
			value = self.operands
			return value
		else:
			raise NotImplementedError(f"SymbolicBool(operator={self.operator.name}, operands={self.operands}).evaluate")


class SymbolicInt(SymbolicExpression):
	"Herbrand model of Python computation. Symbolic `int` value."
	
	class Operator(Enum):
		CONST = 'const'
		ARG = 'arg'
		FOR = 'for'
		LEN = 'len'
		ITEM = 'item'
		CALL = 'call'
		LOOP = 'loop'
		GEN = 'gen'
		
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
	def _const(cls, value:Optional[int]):
		"Integer constant."
		
		if value is None: value = 0
		
		if not isinstance(value, int):
			raise ValueError("`value` must be an int.")
		
		return cls(cls.Operator.CONST, value)
	
	@classmethod
	def _generator(cls, loop_id, length):
		if not isinstance(loop_id, str):
			raise ValueError
		if not isinstance(length, SymbolicInt):
			raise ValueError
		
		return cls(cls.Operator.GEN, (loop_id, length))
	
	@classmethod
	def _arg_len(cls, seq:SymbolicExpression):
		"Length of a collection (integer)."
		
		if not isinstance(seq, SymbolicExpression):
			raise ValueError
		
		return cls(cls.Operator.LEN, (seq,))
	
	@classmethod
	def _arg_item(cls, seq:SymbolicExpression, index:SymbolicExpression):
		"Integer element of a collection."
		
		if not isinstance(seq, SymbolicExpression):
			raise ValueError
		if not isinstance(index, SymbolicExpression):
			raise ValueError
		
		return cls(cls.Operator.ITEM, (seq, index))
	
	def __bool__(self):
		return bool(self != 0)
	
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
	
	def __tostring(self, parent_op):
		if self.operator == self.Operator.CONST:
			return str(self.operands)
		elif self.operator == self.Operator.ARG:
			return self.operands[0] + "." + self.operands[1]
		elif self.operator == self.Operator.LOOP:
			return self.operands[0] + "." + self.operands[1]
		elif self.operator == self.Operator.FOR:
			return "$" + (self.operands[0] if (self.operands[1] is None) else self.operands[0] + "." + self.operands[1])
		elif self.operator == self.Operator.ITEM:
			return str(self.operands[0]) + "[" + str(self.operands[1]) + "]"
		elif self.operator == self.Operator.LEN:
			return "len(" + str(self.operands[0]) + ")"
		elif self.operator == self.Operator.GEN:
			return str(self.operands[0]) + " in range(" + str(self.operands[1]) + ")"
		
		ops = []
		for op in self.operands:
			try:
				ts = op.__tostring
			except AttributeError:
				sop = str(op)
			else:
				sop = ts(self.operator)
			ops.append(sop)

		if parent_op is not None:		
			priority = {
				self.Operator.ADD: 1,
				self.Operator.SUB: 1,
				self.Operator.MUL: 2,
				self.Operator.MOD: 2,
				self.Operator.ARG: 3,
				self.Operator.CONST: 3,
				self.Operator.ITEM: 3
			}
			
			try:
				self_priority = priority[self.operator]
				parent_priority = priority[parent_op]
			except KeyError:
				raise NotImplementedError(str(self.operator) + ", " + str(parent_op))
			
			brackets = self_priority <= parent_priority
		else:
			brackets = False
		
		symbol = {
			self.Operator.ADD: "+",
			self.Operator.SUB: "-",
			self.Operator.MUL: "*",
			self.Operator.XOR: "^",
			self.Operator.MOD: "%"
		}
		
		return ("(" if brackets else "") + (" " + symbol[self.operator] + " ").join(ops) + (")" if brackets else "")
	
	def __str__(self):
		return self.__tostring(None)
	
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
		elif self.operator == self.Operator.CONST:
			value = self.operands
			return value
		else:
			raise NotImplementedError(f"SymbolicInt(operator={self.operator.name}, operands={self.operands}).evaluate")
	
	def to_bytes(self, length, byteorder, signed):
		yield self


class SymbolicList(SymbolicExpression):
	"Symbolic mutable list of variable length."
	
	class Operator(Enum):
		CONST = 'const'
		ARG = 'arg'
		FOR = 'for'
		LOOP = 'loop'
		
		CHAIN = 'chain'
		#PRODUCT = 'product'
	
	@classmethod
	def _const(cls, value):
		if value is None:
			value = []
		
		if not isinstance(value, tuple|list):
			raise ValueError(f"Value provided to constant SymbolicList must be tuple or list, got {type(value).__name__}.")
		
		value = list(value)
		
		return SymbolicList(cls.Operator.CONST, value)
	
	@classmethod
	def _chain(cls, *values):
		return cls(cls.Operator.CHAIN, tuple(SymbolicList(_value) for _value in values))
	
	#@classmethod
	#def _product(cls, *values):
	#	return cls(cls.Operator.PRODUCT, tuple(SymbolicList(_value) for _value in values))
	
	__hash__ = None # mutable object
	
	def __str__(self):
		if self.operator == self.Operator.CONST:
			return "[" + ", ".join(str(_op) for _op in self.operands) + "]"
			#return ".list." + str(abs(self._hash()))[-4:]
		elif self.operator == self.Operator.ARG:
			return self.operands[0] + "." + self.operands[1]
		elif self.operator == self.Operator.LOOP:
			return self.operands[0] + "." + self.operands[1]
		elif self.operator == self.Operator.FOR:
			return "$" + (self.operands[0] if (self.operands[1] is None) else self.operands[0] + "." + self.operands[1])
		elif self.operator == self.Operator.CHAIN:
			return " + ".join(str(_op) for _op in self.operands)
		else:
			raise NotImplementedError
	
	def _len(self):
		if self.operator == self.Operator.CONST:
			return SymbolicInt(len(self.operands))
		elif self.operator == self.Operator.CHAIN:
			r = SymbolicInt(0)
			for op in self.operands:
				r += op._len()
			return r
		elif self.operator == self.Operator.ARG or self.operator == self.Operator.FOR:
			return SymbolicInt._arg_len(self)
		else:
			raise NotImplementedError("len: " + str(self.operator.name))
	
	def __len__(self):
		raise NotImplementedError("Use _len()")
	
	def __getitem__(self, index):
		index = SymbolicInt(index)
		
		if self.operator == self.Operator.CONST and index.operator == SymbolicInt.Operator.CONST:
			return self.operands[index.operands]
		else:
			return SymbolicInt._arg_item(self, index)
	
	def __iter__(self):
		for n in trace_loop(self._len()):
			yield self[n]
	
	def append(self, element):
		one = self.__class__(self)
		two = self.__class__([element])
		new = one + two
		self.operator = new.operator
		self.operands = new.operands
	
	def extend(self, sequence):
		one = self.__class__(self)
		two = self.__class__(sequence) # TODO: handle generators
		new = one + two
		self.operator = new.operator
		self.operands = new.operands
	
	def __add__(self, other):
		other = self.__class__(other)
		if self.operator == other.operator == self.Operator.CONST:
			return self.__class__(self.operands + other.operands)
		else:
			return self._chain(self, other)
	
	def __bool__(self):
		cmp = Comparator(self._len() == 0)
		try:
			return boolean_tests[cmp]
		except KeyError:
			raise BooleanTest(cmp)




#class SymbolicArray(SymbolicExpression):
#	def __class_getitem__(cls, arg):
#		sizes, types = arg
#		return type(f'SymbolicArray[{sizes}, {[_type.__name__ if hasattr(_type, "__name__") else str(_type) for _type in types]}]', (cls,), {'types':types, 'sizes':sizes})
#	
#	class Operator(Enum):
#		CONST = 'const'
#	
#	@classmethod
#	def deserialize(cls, data):
#		print(cls.sizes, cls.types)
#		return cls(cls.CONST, 



def stack(*funcs):
	s = []
	frame = inspect.currentframe()
	while frame.f_back:
		frame = frame.f_back
		s.append(frame)
	
	n = 0
	while any(_func.__code__ in [_frame.f_code for _frame in s[n:]] for _func in funcs):
		n += 1
	return s[n:]


def build_args(fn, cls=None, Field=None, Array=None):
	func_name = fn.__name__
	args = []
	fas = inspect.getfullargspec(fn)
	for var_name in fas.args:
		try:
			type_ = fas.annotations[var_name]
		except KeyError:
			type_ = cls
		
		if type_ == int:
			arg = SymbolicInt._arg(func_name, var_name)
		elif type_ == list:
			arg = SymbolicList._arg(func_name, var_name)
		elif hasattr(type_, 'deserialize'):
			try:
				arg = type_.deserialize(iter([SymbolicInt._arg(func_name, var_name)]))
			except TypeError:
				arg = type_.deserialize(Array, Field, iter(SymbolicList._arg(func_name, var_name)))
		else:
			raise NotImplementedError
		
		args.append(arg)
	return args


def build_value(value):
	if isinstance(value, SymbolicExpression):
		return value
	elif isinstance(value, bool):
		return SymbolicInt(value)
	elif isinstance(value, int):
		return SymbolicInt(value)
	elif isinstance(value, list):
		return SymbolicList([build_value(_element) for _element in value])
	elif isinstance(value, Generator|chain):
		contents = []
		while True:
			try:
				element = next(value)
			except StopIteration:
				break
			else:
				contents.append(element)
		return SymbolicList(contents)
	elif hasattr(value, 'serialize'):
		return value
	else:
		raise NotImplementedError(f"Could not create symbolic value of type: {type(value).__name__}.")


class SymbolicArray(Array):
	StorageType = SymbolicList
	Storage = build_value
	cast = SymbolicInt
	result = SymbolicList


def build_for(value, loop_id, name):
	try:
		return value._for(loop_id, name)
	except AttributeError:
		print(type(value))
		return value.__class__(value.serialize()._for(loop_id, name))


def trace_tests(func):
	try:
		result = func()
	
	except (ArithmeticError, SpecialError) as error:
		return {frozenset(boolean_tests.items()): error}
	
	except LoopIteration as loop_iteration:
		#print(" restarting loop iteration")
		loop_id, dependencies, initialization, iteration = loop_iteration.args
		return {frozenset(boolean_tests.items()): (loop_id, dependencies, initialization, iteration)}
	
	except BooleanTest as test:
		tested = test.args[0]
		
		boolean_tests[tested] = True
		yes_trace = trace_tests(func)
		
		boolean_tests[tested] = False
		no_trace = trace_tests(func)
		
		del boolean_tests[tested]
		
		result = dict()
		result.update(yes_trace)
		result.update(no_trace)
		return result
	
	else:
		if result is NotImplemented:
			raise RuntimeError(f"`NotImplemented` returned from {func}.")
		return {frozenset(boolean_tests.items()): result}


def trace_loop(length):
	fs = stack(trace_loop)
	for eframe in fs:
		instruction = [_instr for _instr in get_instructions(eframe.f_code) if _instr.offset == eframe.f_lasti].pop()
		if instruction.baseopname != 'FOR_ITER':
			break
	#print()
	
	n = 0
	cframe = fs[n]
	loop_id = str(cframe.f_lineno)
	while cframe.f_code.co_name[0] in {'<', '_'}:
		n += 1
		cframe = fs[n]
		loop_id = loop_id + "." + str(cframe.f_lineno)
	funame = cframe.f_code.co_name
	loop_id = funame + "." + loop_id + "." + str(abs(hash(length)))
	
	index = SymbolicInt._for(loop_id, None)
	length = SymbolicInt(length)
	test = (index < length)._while(loop_id)
	
	try:
		dependencies, initialization = active_loops[loop_id]
	except KeyError:
		initialization = {}
		dependencies = frozenset(active_loops.keys())
		active_loops[loop_id] = dependencies, initialization
	
	unsupported_types = Generator | type | Callable
	
	if test:
		for frame in fs:
			if frame == eframe: break
			frame_id = ".".join(str(_f.f_lineno) for _f in fs[fs.index(frame):fs.index(eframe)])
			initialization[frame_id] = {}
			before = {}
			for name, value in frame.f_locals.items():
				if isinstance(value, unsupported_types): continue
				value = build_value(value)
				variable = build_for(value, loop_id, name + "." + str(frame.f_lineno))
				comparator = Comparator(variable)
				if comparator != Comparator(value):
					initialization[frame_id][comparator] = value
				before[name] = build_for(value, loop_id, name + "." + str(frame.f_lineno))
			frame.f_locals.update(before)
			del before
		
		#print("before")
		yield index
		#print("after")
		
		iteration = {}
		for frame in fs:
			if frame == eframe: break
			frame_id = ".".join(str(_f.f_lineno) for _f in fs[fs.index(frame):fs.index(eframe)])
			
			after = {}
			for name, value in frame.f_locals.items():
				if isinstance(value, unsupported_types): continue
				value = build_value(value)
				after[name] = value
			
			iteration[frame_id] = {}
			for name, value in after.items():
				variable = build_for(value, loop_id, name + "." + str(frame.f_lineno))
				comparator = Comparator(variable)
				if comparator != Comparator(value):
					iteration[frame_id][comparator] = value
					if comparator not in initialization[frame_id]:
						initialization[frame_id][comparator] = value.__class__(None)
				else:
					if comparator in initialization[frame_id]:
						del initialization[frame_id][comparator]
			
			del after
		
		#print("end")
		#print("after", initialization.keys(), iteration.keys())
		raise LoopIteration(loop_id, dependencies, initialization, iteration)
	else:
		yield SymbolicInt._generator(loop_id, length)
		
		for frame in fs:
			if frame == eframe: break
			frame_id = ".".join(str(_f.f_lineno) for _f in fs[fs.index(frame):fs.index(eframe)])
			final = {}
			for name, value in frame.f_locals.items():
				if isinstance(value, unsupported_types): continue
				value = build_value(value)
				variable = build_for(value, loop_id, name + "." + str(frame.f_lineno))
				#print("end", initialization.keys())
				if frame_id in initialization and Comparator(variable) in initialization[frame_id]:
					final[name] = value._loop(loop_id, name)
			frame.f_locals.update(final)
			del final
	
	del active_loops[loop_id]


def trace(fn, cls=None, Field=None, Array=None):
	globals_ = {}
	globals_.update(fn.__globals__)
	cfn = fn.__class__(fn.__code__, globals_)
	globals_['range'] = trace_loop
	closure = lambda: build_value(cfn(*build_args(fn, cls, Field, Array)))
	return trace_tests(closure)


def print_symeval(sv):
	for kk, vv in sv.items():
		for k, b in kk:
			print("+" if b else "-", k)
		if isinstance(vv, Exception):
			print(" raise", str(vv))
		elif isinstance(vv, tuple):
			loop_id, dependencies, initialization, iteration = vv
			
			for frame_id, values in initialization.items():
				for variable, value in values.items():
					print("", variable, ":=", str(value))
			print(" repeat", str(loop_id) + ":", ", ".join(str(_dep_id) for _dep_id in dependencies))
			for frame_id, values in iteration.items():
				for variable, value in values.items():
					print(" ", variable, ":=", str(value))
		else:
			print(" return", str(vv))
		print()


def f(a:int, b:int, c:int) -> int:
	return a + b + c


def g(a:int, b:int) -> int:
	if a > b:
		return a
	else:
		return b


def h1(a:int) -> int:
	r = 0
	if a > 2:
		for n in range(a):
			if n > 3:
				r += n
			else:
				r -= n
	else:
		for n in range(a):
			if n > 3:
				r += 1
			else:
				r -= 1
	return a


def h2(a:int) -> list:
	r = []
	for n in range(a):
		r.append(n)
	return r


def h3(a:int) -> list:
	return [_n + 1 for _n in range(a)]


def h4(a:int) -> list:
	r = []
	for n in range(a):
		r.append(n + 1)
	return r


def h5(a:int) -> list:
	def h5a(b:list):
		return [_b + 1 for _b in b]
	
	return h5a(_a + 2 for _a in range(a))


def h6(a:int, b:int) -> int:
	if a > b:
		r = 0
	else:
		r = 1
	
	for i in range(a):
		r += i
		for j in range(b):
			r -= j
	return r


def h7(m:int, n:int) -> list:
	r = []
	for a, b in zip(range(m), range(n)):
		r.append((a, b))
	return r


def h8(a:int, b:int) -> int:
	if a > b:
		r = 0
	else:
		r = 1
	
	for i in range(a):
		r += i
	
	for j in range(b):
		r -= j
	
	return r


def h9() -> list:
	def h9a(g):
		l = list(sum(_g, 0) for _g in g)
		print("received", l)
		return l
		#assert len(list(g)) == 8
	
	return h9a(range(n) for n in range(4))


def h10(l:list) -> list:
	def summe(g):
		r = []
		for x in g:
			r.append(x + 1)
		return r
	
	return summe(build_value(_n * 2 for _n in l))


def slen(value):
	try:
		return value._len()
	except AttributeError:
		return len(value)


if __debug__ and __name__ == '__main__':
	#print_symeval(trace(h10))
	
	#quit()
	
	from fields import Galois
	from operations import Linear
	import operations
	
	Rijndael = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	Rijndael.logarithm = build_value(Rijndael.logarithm)
	Rijndael.exponent = build_value(Rijndael.exponent)
	Rijndael.deserialize = classmethod(lambda cls, data: Rijndael(next(data)))
	
	operations.range = trace_loop
	operations.len = slen
	
	print_symeval(trace(Linear.__add__, Linear, Rijndael, lambda _values, _sizes, _types: Backing.deserialize(_values, _sizes, _types, SymbolicArray, None)))









































































































quit()



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
		if frame.f_code.co_name in {'__eq__', 'srange', '_hash', '__hash__', 'product', 'len', 'min', 'max', '__init__', 'build_value_args'}:
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
		while frame.f_code.co_name in {'<genexpr>', '__iter__', 'sproduct', '_const', '__init__', 'build_value_args'} or '<lambda>' in frame.f_code.co_name:
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


def build_value_args(fn, selfcls, scalar, replace, n=0):
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
			subargs, n_after = build_value_args(t.__init__, t, scalar, replace, n)
			args.append((lambda t, subargs: lambda: t(*subargs()))(t, subargs))
			n = n_after
		else:
			raise NotImplementedError(f"type: {t}")
	
	return (lambda: [_arg() for _arg in args]), n


def trace(fn, selfcls=None, scalar=None, replace=None):
	boolean_tests.clear()
	
	sym_args, n = build_value_args(fn, selfcls, scalar, replace)
	
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
		#print((Rijndael.__name__ + '.') + fn.__name__ + '(' + ', '.join(repr(_arg) for _arg in build_value_args(fn, Rijndael, None, {Rijndael:SymbolicRijndael})[0]()) + ')')
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
		#print((Linear.__name__ + '.') + fn.__name__ + '(' + ', '.join(repr(_arg) for _arg in build_value_args(fn, Linear, Rijndael, {Rijndael:SymbolicRijndael, Linear:SymbolicLinear})[0]()) + ')')
		print(fn.__qualname__)
		print_symeval(trace(fn, Linear, Rijndael, {Rijndael:SymbolicRijndael, Linear:SymbolicLinear}))
	'''

