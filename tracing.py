#!/usr/bin/python3


from utils import singleton, set_sm_range
from memory import Array, Table
from sys import settrace
from inspect import getsourcelines, getfullargspec, currentframe
from typing import Self, TypeVar
from collections import defaultdict
from ctypes import pythonapi, py_object, c_int


class Term:
	def __init__(self, mnemonic, operands):
		self.mnemonic = mnemonic
		self.operands = [_operand._SymbolicInt__value if hasattr(_operand, '_SymbolicInt__value') else _operand for _operand in operands]
		if not all(isinstance(_op, self.__class__ | str | int | None) for _op in self.operands):
			raise TypeError("One of operands is neither Term, str, int nor None.")
	
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


unary_arithmetics = 'neg', 'plus'
binary_arithmetics = 'add', 'sub', 'mul', 'mod', 'pow', 'xor'
binary_comparisons = 'eq', 'ne', 'ge', 'lt', 'gt', 'le'


class BooleanTest(BaseException):
	pass


class EnterLoop(BaseException):
	pass


@singleton
def Arithmetics():
	operations = {}
	
	def make_unary_closure(name):
		return lambda one: one.__class__(Term(name, [one]))
	
	def make_binary_closure(name):
		return lambda one, two: one.__class__(Term(name, [one, one.__class__(two)]))
	
	def make_reversed_closure(name):
		return lambda one, two: one.__class__(Term(name, [one.__class__(two), one]))
	
	for name in unary_arithmetics:
		operations[f'__{name}__'] = make_unary_closure(name)
	
	for name in binary_arithmetics:
		operations[f'__{name}__'] = make_binary_closure(name)
		operations[f'__r{name}__'] = make_reversed_closure(name)
	
	for name in binary_comparisons:
		operations[f'__{name}__'] = make_binary_closure(name)
	
	return type('Arithmetics', (), operations)


class SymbolicInt(Arithmetics):
	"Scalar value."
	
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
			return self.__class__(Term('eq', [self.__value, other.__value]))
		except AttributeError:
			return NotImplemented
	
	__hash__ = None
	
	def __bool__(self):
		#print("boolean test", self.__value)
		try:
			return self._trace__tests[self.__value]
		except KeyError:
			raise BooleanTest(self.__value)


class SymbolicPtr(Arithmetics):
	def __init__(self, value, length=None):
		try:
			self.__value = value.__value
			self.__length = value.__length
		except AttributeError:
			self.__value = value
			self.__length = length
		else:
			assert length is None
		
		if not isinstance(self.__value, Term | int):
			raise TypeError(f"Value should be a Term or int, got {type(self.__value).__name__} instead.")
	
	__hash__ = None
	
	def __len__(self):
		return self.__length
	
	def symbolic_length(self):
		return self.__length
	
	def __getitem__(self, index):
		if hasattr(index, 'start') and hasattr(index, 'stop'):
			return SymbolicArray(Term('getslice', [self.__value, index.start]), index.stop - index.start)
		else:
			return SymbolicInt(Term('getitem', [self.__value, index]))
	
	def __setitem__(self, index, value):
		self._trace__traces.append(Term('setitem', [self.__value, index, value]))


class SymbolicFunction(Arithmetics):
	def __init__(self, value):
		try:
			self.__value = value.__value
		except AttributeError:
			self.__value = value
	
	__hash__ = None
	
	def __call__(self, *args):
		call = Term('call', [self.__pointer, Term('args', args)])
		self._trace__traces.append(call)
		return call


class SymbolicArray(Array):
	"Single-dimensional array (addressed by ints), whose elements may be scalars or other arrays."
	
	StorageType = SymbolicPtr
	Storage = SymbolicPtr
	cast = SymbolicInt
	
	#def __iter__(self):
	#	t = Term('loop', [self._trace__loops])
	#	n = SymbolicInt(t)
	#	
	#	assert 0 <= n < self.symbolic_length()
	#	yield self[n]


@set_sm_range
def sm_range(n):
	lineno = SymbolicArray._trace__loops
	if lineno not in SymbolicArray._trace__loop_entered:
		raise EnterLoop(lineno)
	
	t = Term('loop', [lineno])
	i = SymbolicInt(t)
	
	assert 0 <= i < n
	yield i


class SymbolicTable(Table):
	"Multi-dimensional tables (addressed by tuples of ints), whose elements may be tables, arrays or scalars."
	StorageType = SymbolicPtr
	Storage = SymbolicPtr
	cast = SymbolicInt


Scalar = TypeVar('Scalar')


def trace(fn, cls, scl):
	inside = False
	lines = set()
	loops = set()
	branches = defaultdict(set)
	prev_lineno = None
	
	fname = fn.__qualname__
	
	def trace_fn(frame, event, param):
		nonlocal inside
		
		if event == 'call' and frame.f_code.co_qualname.startswith('Arithmetics.'):
			inside = False
		elif event == 'call' and frame.f_code.co_qualname == fname:
			inside = True
		
		if inside:
			return trace_do
	
	def trace_do(frame, event, param):
		nonlocal inside, prev_lineno
		
		lineno = frame.f_lineno
		branches[prev_lineno].add(lineno)
		prev_lineno = lineno
		
		SymbolicArray._trace__loops = lineno # TODO
		inside = True

		if event == 'return' and frame.f_code.co_qualname == fname:
			inside = False
		elif event == 'line':
			if lineno in lines and lineno not in loops:
				ls, sl = getsourcelines(frame.f_code)
				loops.add(lineno)
				if ls[lineno - sl].strip().startswith('for '):
					print("loop", frame.f_code.co_qualname, lineno, dict((_name, _value) for (_name, _value) in frame.f_locals.items()))
					print(ls[lineno - sl])
					#raise EnterLoop
			else:
				lines.add(lineno)
		
		return trace_do
	
	asp = getfullargspec(fn)
	types = []
	args = []
	for n, argname in enumerate(asp.args):
		arg_cls = fn.__annotations__.get(argname, cls)
		
		if arg_cls == Self:
			arg_cls = cls
			c_backing = arg_cls.c_backing
		elif isinstance(arg_cls, TypeVar) and arg_cls.__name__ == 'Scalar':
			arg_cls = scl
			c_backing = arg_cls.c_backing
		elif arg_cls == int:
			c_backing = 'i32'
		else:
			c_backing = arg_cls.c_backing
		
		term = Term('arg', [c_backing, n])
		types.append(arg_cls)
		args.append(term)
	
	def symeval():
		assert Arithmetics._trace__traces is None
		
		try:
			Arithmetics._trace__traces = []
			
			aa = []
			for type_, arg in zip(types, args):
				if type_ == int:
					a = SymbolicInt(arg)
				else:
					a = type_.symbolic_create(arg)
				aa.append(a)
			
			result = fn(*aa)
			traces = Arithmetics._trace__traces
			Arithmetics._trace__traces = None
			return {frozenset(Arithmetics._trace__tests.items()): [traces, result]}
		
		except (IndexError, ArithmeticError) as error:
			traces = Arithmetics._trace__traces
			Arithmetics._trace__traces = None
			return {frozenset(Arithmetics._trace__tests.items()): [traces, error]}
		
		except AssertionError as error:
			traces = Arithmetics._trace__traces
			Arithmetics._trace__traces = None
			return {}
		
		except EnterLoop as loop:
			lineno = loop.args[0]
			assert lineno not in SymbolicArray._trace__loop_entered
			SymbolicArray._trace__loop_entered.add(lineno)
			
			traces = Arithmetics._trace__traces
			Arithmetics._trace__traces = None
			
			enter_loop = {frozenset(Arithmetics._trace__tests.items()): [traces, (lineno, 'enter')]}
			exit_loop = symeval()
			
			exit_cond = frozenset({(lineno, 'exit')})
			
			result = dict()
			result.update(enter_loop)
			result.update({_cond | exit_cond : _value for (_cond, _value) in exit_loop.items()})
			return result
		
		except BooleanTest as test:
			tested = test.args[0]
			
			Arithmetics._trace__traces = None
			assert test not in Arithmetics._trace__tests
			
			Arithmetics._trace__tests[tested] = True
			yes_trace = symeval()
			
			Arithmetics._trace__tests[tested] = False
			no_trace = symeval()
			
			del Arithmetics._trace__tests[tested]
			
			tests = frozenset(Arithmetics._trace__tests.items())
			
			yes_test = frozenset({(tested, True)})
			no_test = frozenset({(tested, False)})
			
			result = dict()
			result.update({yes_cond | yes_test : yes_value for (yes_cond, yes_value) in yes_trace.items()})
			result.update({no_cond | no_test : no_value for (no_cond, no_value) in no_trace.items()})
			return result
	
	Arithmetics._trace__traces = None
	Arithmetics._trace__tests = {}
	SymbolicArray._trace__loops = None
	SymbolicArray._trace__loop_entered = set()
	#settrace(trace_fn)
	try:
		trace_result = symeval()
	finally:
		#settrace(None)
		del Arithmetics._trace__traces
		del Arithmetics._trace__tests
		del SymbolicArray._trace__loops
		del SymbolicArray._trace__loop_entered
	
	return trace_result


def test_basic():
	x = SymbolicInt(Term('arg', ['u8', 0]))
	y = SymbolicInt(Term('const', ['u8', 77]))
	print(x + y)
	
	a = SymbolicArray(SymbolicInt(Term('arg', ['*u8', 1])), 10)
	
	t = Trace()
	
	with t:
		a[1] = 1
		a[2] = a[1] + a[0]
		a[1] = 2 - a[0] % 9
		a[3] = x
		a[x] = y
	
	for k in t.trace:
		print(k)


def get_result(x):
	if isinstance(x, int):
		return x
	else:
		return x._SymbolicInt__value



if __name__ == '__main__':
	def iterate_me():
		frame = currentframe().f_back
		vars_orig = dict(frame.f_locals)
		vars_before = dict()
		for v in vars_orig.keys():
			vars_before[v] = SymbolicInt(Term('loop', [0, v]))
		frame.f_locals.update(vars_before)
		pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0)) # FIXME: not needed in python >= 3.13
		
		yield SymbolicInt(Term('loop', [0, '_']))
		
		frame = currentframe().f_back
		vars_after = dict(frame.f_locals)		
		for v in vars_before.keys():
			if get_result(vars_before[v]) == get_result(vars_after[v]):
				print("variable unmodified:", v)
				vars_after[v] = vars_orig[v]
		frame.f_locals.update(vars_after)
		pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0)) # FIXME: not needed in python >= 3.13
	
	def loop_me(e):
		k = 0
		l = 0
		for i in iterate_me():
			if k > 0:
				k += i + l
			else:
				k -= i * e
			
			if l > 0:
				l += 1
				pass
		return k + l
	
	trace_result = trace(loop_me, int, None)
	
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




if False and __name__ == '__main__':
	from aes import Rijndael
	from operations import Linear, Quadratic
	
	class SymbolicRijndael(Rijndael):
		c_backing = 'u8'
		c_length = None
		
		logarithm = SymbolicPtr(Term('const', ['*u8', 'Rijndael.logarithm']), 256)
		exponent = SymbolicPtr(Term('const', ['*u8', 'Rijndael.exponent']), 256)
		
		@classmethod
		def symbolic_create(cls, term):
			return cls(SymbolicInt(term))
		
		def symbolic_extract(self):
			return get_result(list(self.serialize())[0])
		
		#sum = SymbolicFunction(Term('func', ['*u8,u32→u8', 'Rijndael.sum']))
	
	class SymbolicLinear(Linear):
		c_backing = '*u8'
		c_length = 8
		
		@classmethod
		def symbolic_create(cls, term):
			return cls(SymbolicArray(SymbolicPtr(term, 8), [None], [SymbolicRijndael]))
		
		#def __call__(self, x:SymbolicRijndael) -> SymbolicRijndael:
		#	return super()(x)
	
	#trace_result = trace(Linear.__call__, SymbolicLinear, SymbolicRijndael)
	
	def aaa(x, y):
		if x > y:
			return x + y
		
		k = 0
		for n in sm_range(y):
			k += x * n
		return k
	
	trace_result = trace(aaa, int, None)


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
	
	
	print()
	print()
	
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
		#break
	







