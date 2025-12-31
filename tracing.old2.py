#!/usr/bin/python3


from enum import Enum
from memory import Array, Table
from itertools import chain
import ast
import inspect
from ctypes import pythonapi, py_object, c_int
from functools import reduce
from operator import __mul__
from llvmlite import ir, binding
from collections import Counter, defaultdict


class BooleanTest(BaseException):
	pass


class LoopIteration(BaseException):
	pass


class Statement:
	class Operator(Enum):
		ASSIGN = '='


boolean_tests = {}


class Comparator:
	def __init__(self, expression):
		self.expression = expression
		if not isinstance(self.expression, SymbolicExpression):
			raise ValueError(f"Argument should be Expression, got {type(self.expression).__name__}.")
	
	def __eq__(self, other):
		try:
			if self.expression.operator != other.expression.operator:
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
	
	def __hash__(self):
		if isinstance(self.expression.operands, list|tuple):
			return hash(tuple(chain((self.expression.operator,), (hash(self.__class__(_op) if isinstance(_op, SymbolicExpression) else _op) for _op in self.expression.operands))))
		else:
			return hash((self.expression.operator, self.expression.operands))
	
	def __str__(self):
		return str(self.expression)
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + repr(self.expression) + ')'


class SymbolicExpression:
	def __init__(self, operator, operands=None):
		if operands is None:
			try:
				self.operator = operator.operator
				self.operands = operator.operands
			except AttributeError:
				const = self._const(operator)
				self.operator = const.operator
				self.operands = const.operands
		else:
			self.operator = operator
			self.operands = operands
		
		if not isinstance(self.operator, self.Operator):
			raise ValueError(f"`operator` must be {self.Operator}, got {type(operator)}.")
	
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
	
	__hash__ = None
	
	def __str__(self):
		return " ".join(_b for (_a, _b) in self._print())
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + self.operator.__class__.__name__ + '.' + self.operator.name + ', ' + repr(self.operands) + ')'
	
	def __eq__(self, other):
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


class SymbolicBool(SymbolicExpression):
	ll_type = ir.IntType(1)
	
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
			raise ValueError(f"Unsupported operator: {self.operator}")


class SymbolicInt(SymbolicExpression):
	ll_type = ir.IntType(16)
	
	class Operator(Enum):
		INT = 'int'
		ARG = 'int_arg'
		FOR = 'for'
		
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
	def _arg(cls, number):
		return cls(cls.Operator.ARG, number)
	
	@classmethod
	def _const(cls, value):
		return cls(cls.Operator.INT, int(value))
	
	@classmethod
	def _for(cls, serial, length, order):
		return cls(cls.Operator.FOR, (serial, length, order))
	
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
	
	def __floordiv__(self, other):
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
	
	def _has_for(self):
		if self.operator == self.Operator.FOR:
			return True
		else:
			return super()._has_for()


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


loop_serial = [0]


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


def symeval(func):
	loop_serial.clear()
	loop_serial.append(0)
	
	try:
		result = func()
	
	except (IndexError, ValueError) as error:
		return {frozenset(boolean_tests.items()): error}
	
	except LoopIteration as loop:
		loop_index = loop.args[0]
		loop_range = loop.args[1]
		loop_body = loop.args[2]
		return {frozenset(boolean_tests.items()): (loop_index, loop_range, loop_body)}
	
	except BooleanTest as error:
		tested = error.args[0]
		
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
		return {frozenset(boolean_tests.items()): result}


def srange(length):
	length = SymbolicInt(length)
	
	loop_serial.append(0)
	ls = tuple(loop_serial[:-1])
	
	n = SymbolicInt._for(ls, '', 0)
		
	if n < length:
		loop_vars = {}
		frame = inspect.currentframe().f_back
		pythonapi.PyFrame_FastToLocals(py_object(frame), c_int(0))
		for name, value in frame.f_locals.items():
			loop_vars[name] = SymbolicInt._for(ls, name, value) # initial value
		frame.f_locals.update(loop_vars)
		pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0))
		
		yield n
		
		loop_result = {}
		frame = inspect.currentframe().f_back
		pythonapi.PyFrame_FastToLocals(py_object(frame), c_int(0))
		for name, value in frame.f_locals.items():
			if name not in loop_vars or value is not loop_vars[name]:
				loop_result[name] = value # value after iteration
		
		raise LoopIteration(ls, length, loop_result)
	else:
		new_locals = {}
		frame = inspect.currentframe().f_back
		pythonapi.PyFrame_FastToLocals(py_object(frame), c_int(0))
		for name, value in frame.f_locals.items():
			new_locals[name] = SymbolicInt._for(ls, name, ...) # final value
		frame.f_locals.update(new_locals)
		pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0))
	
	loop_serial.pop()
	loop_serial[-1] += 1


module = ir.Module()

error_func_type = ir.FunctionType(ir.VoidType(), [ir.IntType(8).as_pointer()])
error_func = ir.Function(module, error_func_type, name='error')


def trace(fn, deftype=int):
	n = 0
	sym_args = []
	ll_args = []
	for a in inspect.getfullargspec(fn).args:
		t = None
		try:
			t = fn.__annotations__[a]
		except KeyError:
			try:
				t = fn.__self__
			except AttributeError:
				t = deftype
		
		if t == int:
			sym_args.append(SymbolicInt._arg(n))
			ll_args.append(SymbolicInt.ll_type)
		elif issubclass(t, Rijndael):
			sym_args.append(t(SymbolicInt._arg(n)))
			ll_args.append(SymbolicInt.ll_type)
		else:
			raise NotImplementedError(f"type: {t}")
		
		n += 1
	
	boolean_tests.clear()
	closure = lambda: fn(*sym_args)
	closure.__globals__['range'] = srange
	sv = symeval(closure)
	
	def new_fn(*aa):
		for kk, vv in sv.items():
			for k, b in kk:
				print("+" if b else "-", " ".join(_b for (_a, _b) in k.expression._print()))
			print(" ", type(vv).__name__ + ":", repr(vv))
			print()
	
	
	algo = optimize_conditions(sv)
	
	#compile_function(fn.__name__, SymbolicInt.ll_type, ll_args, algo)
	
	return new_fn


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
