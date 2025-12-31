#!/usr/bin/python3


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
