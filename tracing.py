#!/usr/bin/python3


"Tracing simple Python algorithms, producing symbolic representation that can be optimized."


__all__ = 'SymbolicValue', 'SymbolicArray', 'SymbolicTable', 'transform', 'optimize_expr', 'symbolize', 'trace'


from enum import Enum
from collections import defaultdict
from collections.abc import Iterable
from itertools import chain, product
import ast, inspect
from functools import cmp_to_key
from ctypes import py_object, c_int, pythonapi


class SymbolicValue:
	Type = Enum('SymbolicValue.Type', 'BOOL INT UINT LIST_INT LIST_UINT')
	Mnemonic = Enum('SymbolicValue.Mnemonic', 'CONST PTR FUN ARG IF LOOP_IN LOOP_OUT LOOP_CNT CALL INDEX ADD SUB MUL FLOORDIV MOD NEG SHL POW XOR AND EQ NE GT GE LT LE RANGE PRODUCT LISTCOMP STORE SLICE')
	
	def __init__(self, mnemonic, type_=None, length=None, operands=None):
		if type_ is None and length is None and operands is None:
			try:
				self.__mnemonic = mnemonic.__mnemonic
				self.__type = mnemonic.__type
				self.__length = mnemonic.__length
				self.__operands = mnemonic.__operands
			
			except AttributeError:
				if isinstance(mnemonic, int):
					self.__mnemonic = self.Mnemonic.CONST
					if mnemonic >= 0:
						self.__type = self.Type.UINT
					else:
						self.__type = self.Type.INT
					self.__length = None
					self.__operands = mnemonic
				
				elif isinstance(mnemonic, str | dict):
					raise TypeError(f"Could not convert value to SymbolicValue: {type(mnemonic)}.")
				
				elif isinstance(mnemonic, Iterable):
					self.__mnemonic = self.Mnemonic.CONST
					values = [self.__class__(v) for v in mnemonic]
					t = frozenset(_v.__type for _v in values)
					if t == frozenset({self.Type.INT, self.Type.UINT}):
						self.__type = self.Type.LIST_INT
					elif t == frozenset({self.Type.UINT}):
						self.__type = self.Type.LIST_UINT
					else:
						self.__type = self.Type.LIST_INT
						#raise ValueError(f"List must be flat collection of ints. Got: {values}")
					self.__length = len(values)
					self.__operands = values
				
				else:
					raise TypeError(f"Could not convert value to SymbolicValue: {type(mnemonic)}.")
		
		else:
			try:
				self.__mnemonic = mnemonic.__mnemonic
				self.__type = mnemonic.__type
				self.__length = mnemonic.__length
				self.__operands = mnemonic.__operands
			except AttributeError:
				self.__mnemonic = mnemonic
				self.__type = type_
				self.__length = length
				self.__operands = operands
		
		assert isinstance(self.__length, int) if self.__length is not None else True, str(self.__length)
		assert not isinstance(self.__operands, self.__class__)
		
		if not isinstance(self.__operands, str) and self.__mnemonic == self.Mnemonic.FUN:
			raise ValueError("Function name must be str.")
		
		if not isinstance(self.__operands, list) and self.__mnemonic == self.Mnemonic.IF:
			raise ValueError("Condition operands must be expressions.")
	
	def __getnewargs__(self):
		return self.__mnemonic, self.__type, self.__length, self.__operands
	
	@classmethod
	def _int(cls, v):
		return cls(cls.Mnemonic.CONST, cls.Type.INT, None, v)
	
	@classmethod
	def _uint(cls, v):
		return cls(cls.Mnemonic.CONST, cls.Type.UINT, None, v)
	
	@classmethod
	def _list_int(cls, v):
		l = [cls._int(_v) for _v in v]
		return cls(cls.Mnemonic.CONST, cls.Type.LIST_INT, len(l), l)
	
	@classmethod
	def _list_uint(cls, v):
		l = [cls._uint(_v) for _v in v]
		return cls(cls.Mnemonic.CONST, cls.Type.LIST_UINT, len(l), l)
	
	@classmethod
	def _fun_int(cls, name):
		if not isinstance(name, str):
			raise ValueError("Function name must be str.")
		return cls(cls.Mnemonic.FUN, cls.Type.INT, None, name)
	
	@classmethod
	def _fun_uint(cls, name):
		if not isinstance(name, str):
			raise ValueError("Function name must be str.")
		return cls(cls.Mnemonic.FUN, cls.Type.UINT, None, name)
	
	@classmethod
	def _fun_list_int(cls, name, l):
		return cls(cls.Mnemonic.FUN, cls.Type.LIST_INT, l, name)
	
	@classmethod
	def _fun_list_uint(cls, name, l):
		return cls(cls.Mnemonic.FUN, cls.Type.LIST_UINT, l, name)
	
	@classmethod
	def _arg_int(cls, v):
		return cls(cls.Mnemonic.ARG, cls.Type.INT, None, v)
	
	@classmethod
	def _arg_uint(cls, v):
		return cls(cls.Mnemonic.ARG, cls.Type.UINT, None, v)
	
	@classmethod
	def _arg_list_int(cls, v, l):
		return cls(cls.Mnemonic.ARG, cls.Type.LIST_INT, l, v)
	
	@classmethod
	def _arg_list_uint(cls, v, l):
		return cls(cls.Mnemonic.ARG, cls.Type.LIST_UINT, l, v)
	
	@classmethod
	def _ptr_int(cls, v):
		return cls(cls.Mnemonic.PTR, cls.Type.INT, None, v)
	
	@classmethod
	def _ptr_uint(cls, v):
		return cls(cls.Mnemonic.PTR, cls.Type.UINT, None, v)
	
	@classmethod
	def _ptr_list_int(cls, v, l):
		return cls(cls.Mnemonic.PTR, cls.Type.LIST_INT, l, v)
	
	@classmethod
	def _ptr_list_uint(cls, v, l):
		return cls(cls.Mnemonic.PTR, cls.Type.LIST_UINT, l, v)
	
	@classmethod
	def _if(cls, c, yes, no):
		#print("if", yes, no)
		
		if isinstance(yes, int):
			yes = cls(yes)
		if isinstance(no, int):
			no = cls(no)
		
		if yes.__type != no.__type:
			raise ValueError
		return cls(cls.Mnemonic.IF, yes.__type, yes.__length, [c, yes, no])
	
	@classmethod
	def _loop_in(cls, loop_no, var_name, before):
		return cls(cls.Mnemonic.LOOP_IN, before.__type, before.__length, [loop_no, var_name, before])
	
	@classmethod
	def _loop_out(cls, loop_no, var_name, after):
		return cls(cls.Mnemonic.LOOP_OUT, after.__type, after.__length, [loop_no, var_name, after])
	
	@classmethod
	def _loop_cnt(cls, loop_id, length):
		if not isinstance(loop_id, str):
			raise ValueError(f"loop_id should be str. Got: {loop_id}")
		return cls(cls.Mnemonic.LOOP_CNT, cls.Type.UINT, None, [loop_id, length])
	
	@classmethod
	def _range(cls, n):
		return cls(cls.Mnemonic.RANGE, cls.Type.LIST_UINT, n, None)
	
	@classmethod
	def _product(cls, *nn):
		ll = 1
		for n in nn:
			ll *= n
		return cls(cls.Mnemonic.PRODUCT, cls.Type.LIST_UINT, ll, nn)
	
	@classmethod
	def _listcomp(cls, n):
		return cls(cls.Mnemonic.LISTCOMP, cls.Type.LIST_UINT, n, None)
	
	def __add__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		if frozenset({self.__type, other.__type}) == frozenset({self.Type.UINT}):
			type_ = self.Type.UINT
			length = None
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT}):
			type_ = self.Type.INT
			length = None
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT, self.Type.UINT}):
			type_ = self.Type.INT
			length = None
		
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.LIST_UINT}):
			type_ = self.Type.LIST_UINT
			length = self.__length + other.__length
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.LIST_INT}):
			type_ = self.Type.LIST_INT
			length = self.__length + other.__length
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.LIST_INT, self.Type.LIST_UINT}):
			type_ = self.Type.LIST_INT
			length = self.__length + other.__length
		
		else:
			raise TypeError(f"Could not __add__ following types: {self.__type.name}, {other.__type.name}")
		
		return self.__class__(self.Mnemonic.ADD, type_, length, [self, other])
	
	def __sub__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		if frozenset({self.__type, other.__type}) == frozenset({self.Type.UINT}):
			type_ = self.Type.INT
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT}):
			type_ = self.Type.INT
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT, self.Type.UINT}):
			type_ = self.Type.INT
		
		else:
			raise TypeError(f"Could not __sub__ following types: {self.__type.name}, {other.__type.name}")
		
		return self.__class__(self.Mnemonic.SUB, type_, None, [self, other])
	
	def __mod__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		if other.__type == self.Type.UINT and self.__type in [self.Type.INT, self.Type.UINT]:
			type_ = self.Type.UINT
		else:
			raise TypeError(f"Could not __mod__ following types: {self.__type.name}, {other.__type.name}")
		
		return self.__class__(self.Mnemonic.MOD, type_, None, [self, other])
	
	def __xor__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented

		if frozenset({self.__type, other.__type}) == frozenset({self.Type.UINT}):
			type_ = self.Type.UINT
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT}):
			type_ = self.Type.INT
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT, self.Type.UINT}):
			type_ = self.Type.INT
		
		else:
			raise TypeError(f"Could not __xor__ following types: {self.__type.name}, {other.__type.name}")
		
		return self.__class__(self.Mnemonic.XOR, type_, None, [self, other])
	
	def __rxor__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return other.__xor__(self)
	
	def __mul__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		if frozenset({self.__type, other.__type}) == frozenset({self.Type.UINT}):
			type_ = self.Type.UINT
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT}):
			type_ = self.Type.INT
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT, self.Type.UINT}):
			type_ = self.Type.INT
		
		else:
			raise TypeError(f"Could not __mul__ following types: {self.__type.name}, {other.__type.name}")
		
		return self.__class__(self.Mnemonic.MUL, type_, None, [self, other])
	
	def __rmul__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return other * self
	
	def __floordiv__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		if frozenset({self.__type, other.__type}) == frozenset({self.Type.UINT}):
			type_ = self.Type.UINT
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT}):
			type_ = self.Type.INT
		elif frozenset({self.__type, other.__type}) == frozenset({self.Type.INT, self.Type.UINT}):
			type_ = self.Type.INT
		
		else:
			raise TypeError(f"Could not __floordiv__ following types: {self.__type.name}, {other.__type.name}")
		
		return self.__class__(self.Mnemonic.FLOORDIV, type_, None, [self, other])
	
	def __rfloordiv__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return other // self
	
	def __pow__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		if other.__type != self.Type.UINT:
			raise TypeError
		
		if self.__type not in (self.Type.INT, self.Type.UINT):
			raise TypeError
		
		return self.__class__(self.Mnemonic.POW, self.__type, None, [self, other])
	
	def __rpow__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return other.__pow__(self)
	
	def __abs__(self):
		if self.__type == self.Type.UINT:
			return self
		elif self.__type != self.Type.INT:
			raise TypeError
		
		sign = self.__class__(2) * self.__class__(self.Mnemonic.GE, self.Type.UINT, None, [self, self.__class__(0)]) - self.__class__(1)
		result = sign * self
		#return result
		#r = self.__class__._if(self >= self.__class__(0), self, -self)
		return self.__class__(result.__mnemonic, self.Type.UINT, result.__length, result.__operands)
	
	def __neg__(self):
		return self.__class__(-1) * self
	
	def __lt__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return self.__class__(self.Mnemonic.LT, self.Type.BOOL, None, [self, other])
	
	def __le__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return self.__class__(self.Mnemonic.LE, self.Type.BOOL, None, [self, other])
	
	def __gt__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return self.__class__(self.Mnemonic.GT, self.Type.BOOL, None, [self, other])
	
	def __ge__(self, other):
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return self.__class__(self.Mnemonic.GE, self.Type.BOOL, None, [self, other])
	
	def __eq__(self, other):
		if not tracing:
			try:
				return self.__mnemonic == other.__mnemonic and self.__type == other.__type and self.__length == other.__length and self.__operands == other.__operands
			except AttributeError:
				return NotImplemented
		
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return self.__class__(self.Mnemonic.EQ, self.Type.BOOL, None, [self, other])
	
	def __ne__(self, other):
		if not tracing:
			try:
				return not (self.__mnemonic == other.__mnemonic and self.__type == other.__type and self.__length == other.__length and self.__operands == other.__operands)
			except AttributeError:
				return NotImplemented
		
		try:
			other = self.__class__(other)
		except ValueError:
			return NotImplemented
		
		return self.__class__(self.Mnemonic.NE, self.Type.BOOL, None, [self, other])
	
	def __len__(self):
		if self.__length is None:
			raise TypeError(f"Can not determine length of {self}.")
		else:
			return self.__length
	
	def __iter__(self):
		for n in range(len(self)):
			yield self[n]
	
	def __call__(self, *args):
		if self.__mnemonic != self.Mnemonic.FUN:
			raise TypeError(f"Can not call {self}.")
		
		return self.__class__(self.Mnemonic.CALL, self.__type, self.__length, [self] + list(self.__class__(_arg) for _arg in args))
	
	def __getitem__(self, index):
		global tracing
		
		#print("index", self.__mnemonic, index)
				
		if hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step'):
			if index.step not in [1, None]:
				raise ValueError("Only slices of step 1 (or None) are supported.")
			
			start = index.start
			stop = index.stop			
			length = stop - start
			
			if isinstance(start, self.__class__) and isinstance(stop, self.__class__):
				was_tracing = tracing
				tracing = False
				
				if (start.__mnemonic == stop.__mnemonic == self.Mnemonic.MUL) and \
				    (start.__operands[1] == stop.__operands[1]) and \
				     (stop.__operands[0].__mnemonic == self.Mnemonic.ADD) and \
				      (stop.__operands[0].__operands[1] == SymbolicValue(1)) and \
				       (start.__operands[0] == stop.__operands[0].__operands[0]) and \
				        (start.__operands[1].__mnemonic == self.Mnemonic.CONST):
					length = start.__operands[1].__operands
				elif (start.__mnemonic == stop.__mnemonic == self.Mnemonic.MUL) and \
				      (start.__operands[1] == stop.__operands[1]) and \
				       (start.__operands[0].__mnemonic == stop.__operands[0].__mnemonic == self.Mnemonic.ADD) and \
				        (start.__operands[0].__operands[1].__mnemonic == stop.__operands[0].__operands[1].__mnemonic == self.Mnemonic.CONST) and \
				         (stop.__operands[0].__operands[1].__operands - start.__operands[0].__operands[1].__operands == 1) and \
				          (start.__operands[0].__operands[0] == stop.__operands[0].__operands[0]):
					length = start.__operands[1].__operands
				
				tracing = was_tracing
			
			return self.__class__(self.Mnemonic.SLICE, self.__type, length, [self.__class__(start), self])
		
		if isinstance(index, tuple):
			idx = self.__class__(0)
			l = 1
			for i in index:
				idx += l * i
				l *= i.__operands[1]
			
			index = idx
		
		else:
			try:
				index = self.__class__(index)
			except ValueError:
				return NotImplemented
		
		if index.__type not in (self.Type.INT, self.Type.UINT):
			raise TypeError(f"Can not use {index} as index.")
		
		if self.__mnemonic == self.Mnemonic.PRODUCT:
			# 2 * 2 * 3 = 12
			# k = n % 3
			# j = (n // 3) % 2
			# i = (n // (3 * 2)) % 2
			l = 1
			r = []
			for i in reversed(self.__operands):
				r.append((index // l) % i)
				l *= i
			ret = tuple(reversed(r))
			#print(len(r), len(ret), len(self.__operands), ret)
			return ret
		
		if self.__type == self.Type.LIST_INT:
			type_ = self.Type.INT
		elif self.__type == self.Type.LIST_UINT:
			type_ = self.Type.UINT
		else:
			raise TypeError(f"Can not take item of {self}.")
		
		if index >= self.__length:
			raise IndexError(f"{index} >= {self.__length}")
		
		if self.__mnemonic == self.Mnemonic.RANGE:
			return index
		
		return self.__class__(self.Mnemonic.INDEX, type_, None, [self, index])
	
	def __setitem__(self, index, value):
		try:
			index = self.__class__(index)
		except ValueError:
			return NotImplemented
		
		if index.__type not in (self.Type.INT, self.Type.UINT):
			raise TypeError(f"Can not use {index} as index. indexed={self}")
		
		if self.__type == self.Type.LIST_INT:
			type_ = self.Type.INT
		elif self.__type == self.Type.LIST_UINT:
			type_ = self.Type.UINT
		else:
			raise TypeError(f"Can not set item of {self}.")
				
		try:
			value = self.__class__(value)
		except ValueError:
			return NotImplemented
		
		if value.__type != type_:
			raise TypeError
		
		if index >= self.__length:
			raise IndexError(f"{index} >= {self.__length}")
		
		#if self.__mnemonic != self.Mnemonic.LISTCOMP:
		#	raise TypeError(f"Can not set item of {self}.")
		#
		#self.__operands.append((index, value))
		
		if value.__type == self.Type.UINT:
			self.__type = self.Type.LIST_UINT
		elif value.__type == self.Type.INT:
			self.__type = self.Type.LIST_INT
		else:
			raise TypeError
		
		old = self.__class__(self)
		self.__mnemonic = self.Mnemonic.STORE
		self.__operands = [old, index, value]
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + self.__mnemonic.name + ', ' + self.__type.name + ', ' + repr(self.__length) + ', ' + repr(self.__operands) + ')'
	
	def __bool__(self):
		if self.__mnemonic == self.Mnemonic.GE and self.__operands[0].__mnemonic == self.Mnemonic.CONST and self.__operands[1].__mnemonic == self.Mnemonic.CONST:
			return self.__operands[0].__operands >= self.__operands[1].__operands
		elif self.__mnemonic == self.Mnemonic.GE and self.__operands[0].__mnemonic == self.Mnemonic.LOOP_CNT and self.__operands[1].__mnemonic == self.Mnemonic.CONST:
			if self.__operands[0].__operands[1] <= self.__operands[1].__operands:
				return False
		elif self.__mnemonic == self.Mnemonic.LE and self.__operands[0].__mnemonic == self.Mnemonic.LOOP_CNT and self.__operands[1].__mnemonic == self.Mnemonic.CONST:
			if self.__operands[0].__operands[1] <= self.__operands[1].__operands:
				return True
		elif self.__mnemonic == self.Mnemonic.LT and self.__operands[0].__mnemonic == self.Mnemonic.LOOP_CNT and self.__operands[1].__mnemonic == self.Mnemonic.CONST:
			if self.__operands[0].__operands[1] <= self.__operands[1].__operands:
				return True
		
		state = self._state()
		if state in boolean_values:
			return boolean_values[state]
		else:
			raise BooleanQuery(self)
	
	def _state(self):
		return (self.__mnemonic, self.__type, self.__length, tuple(_op._state() if hasattr(_op, '_state') else _op for _op in self.__operands) if isinstance(self.__operands, list) else self.__operands)
	
	def _print_tree(self, level=0, file=None):
		try:
			if isinstance(self.__operands, str):
				raise TypeError
			oo = iter(self.__operands)
		except TypeError:
			print(" " * level, self.__mnemonic.name, self.__type.name, self.__length, self.__operands, file=file)
		else:
			print(" " * level, self.__mnemonic.name, self.__type.name, self.__length, file=file)
			for operand in oo:
				try:
					operand._print_tree(level + 1, file=file)
				except AttributeError:
					print(" " * (level + 1), operand, file=file)
		if level == 0:
			print(file=file)


boolean_values = {}


class BooleanQuery(BaseException):
	def __init__(self, value):
		self.value = value


def __load_vars():
	outer_frame = inspect.stack()[2].frame
	inner_frame = inspect.stack()[1].frame
	inner_frame.f_locals.update({_k:_v for (_k, _v) in outer_frame.f_locals.items() if not _k.startswith('__')})
	pythonapi.PyFrame_LocalsToFast(py_object(inner_frame), c_int(0))


def __save_vars():
	outer_frame = inspect.stack()[2].frame
	inner_frame = inspect.stack()[1].frame
	outer_frame.f_locals.update({_k:_v for (_k, _v) in inner_frame.f_locals.items() if not _k.startswith('__')})
	pythonapi.PyFrame_LocalsToFast(py_object(outer_frame), c_int(0))


tracing = False


def trace(fn, args):
	global tracing
	tracing = True
	
	boolean_values.clear()
	
	def path():
		try:
			#print(fn.__qualname__, len(args))
			#print("func", fn.__qualname__, inspect.getfullargspec(fn).args, len(args))

			return fn(*args)
		except BooleanQuery as bq:
			state = bq.value._state()
			
			boolean_values[state] = True
			yes = path()
			
			boolean_values[state] = False
			#print("no path", fn.__name__, bq.value)
			no = path()
			
			del boolean_values[state]
			
			if yes is None and no is None:
				return None
			elif yes is None:
				return no
			elif no is None:
				return yes
			else:
				if yes.__class__ != no.__class__:
					raise TypeError("Different classes in conditional.")
				ty, sy = symbolize(yes)
				tn, sn = symbolize(no)
				return ty(SymbolicValue._if(bq.value, sy, sn))
		except (ArithmeticError, IndexError, KeyError) as error: # TODO
			return None
	
	p = path()
	tracing = False
	return p


def trace_loop(__fn, __target, kwargs):
	def sandbox(**__kwargs):
		__frame = inspect.stack()[0].frame
		__frame.f_locals.update(__kwargs)
		for __key in list(__frame.f_locals.keys()):
			if __key.startswith('__'):
				del __frame.f_locals[__key]
		pythonapi.PyFrame_LocalsToFast(py_object(__frame), c_int(0))
		
		try:
			#print("loop", inspect.getfullargspec(__fn).args, len(__target))
			if isinstance(__target, tuple|list):
				__fn(*__target, 0)
			else:
				#print(type(__target).__name__, __target)
				__fn(__target, 0)
		except __Pass:
			pass
		return {_k:_v for (_k, _v) in locals().items() if not _k.startswith('__')}
	
	def path():
		try:
			result = sandbox(**kwargs)
			return result
		except BooleanQuery as bq:
			state = bq.value._state()
			
			boolean_values[state] = True
			yes = path()
			
			boolean_values[state] = False
			no = path()
			
			del boolean_values[state]
			
			if not yes:
				return no
			elif not no:
				return yes
			else:
				result = {}
				for key in yes.keys() | no.keys():
					if key in yes and key in no:
						ty, sy = symbolize(yes[key])
						tn, sn = symbolize(no[key])
						result[key] = ty(SymbolicValue._if(bq.value, sy, sn))
					elif key in yes:
						result[key] = yes[key]
					elif key in no:
						result[key] = no[key]
				return result
		except (ArithmeticError, IndexError, KeyError): # TODO
			return {}
	
	return path()


def symbolize(value):
	if isinstance(value, int):
		return int, value
	elif isinstance(value, SymbolicValue):
		return SymbolicValue, value
	
	try:
		s, *a = value.__getnewargs__()
	except AttributeError:
		return (lambda _x: _x), value
	
	t, s = symbolize(s)
	c = value.__class__
	
	return (lambda _v: c(t(_v), *a)), s


def __loop_body(loop_id, iter_):	
	looped = None
	if tracing:
		def decorator(fn):
			def new_fn(*loop_args):
				*targets, call_id = loop_args
				
				global tracing
				nonlocal looped
				
				if looped is None:
					frame = inspect.stack()[1].frame
					initial = dict(frame.f_locals)
					for key in list(initial.keys()):
						if isinstance(initial[key], type):
							del initial[key]
						elif isinstance(initial[key], int):
							initial[key] = SymbolicValue(initial[key])
					if 'self' in initial:
						del initial['self']
					
					loop_in = {}
					loop_in_copy = {}
					for key, value in initial.items():
						if key.startswith('__'): continue
						t, s = symbolize(value)
						loop_in[key] = t(SymbolicValue._loop_in(loop_id, key, SymbolicValue(s)))
						loop_in_copy[key] = t(SymbolicValue._loop_in(loop_id, key, SymbolicValue(s)))
					
					final = trace_loop(fn, targets, loop_in)
					
					was_tracing = tracing
					tracing = False
					looped_keys = set()
					erase_keys = set(final.keys())
					
					for key in final.keys():
						#if key.startswith('_counter_'):
						#	looped_keys.add(key)
						#	erase_keys.remove(key)
						if key in loop_in and loop_in_copy[key] == final[key]:
							continue
						if key in loop_in and loop_in[key].__class__ != final[key].__class__:
							raise TypeError("Loop variable changed type.")
						looped_keys.add(key)
						erase_keys.remove(key)
					tracing = was_tracing
					
					#final[f'_counter_{loop_id}'] = initial[f'_counter_{loop_id}']
					#initial[f'_counter_{loop_id}'] = counter
					
					def erase_loop_in(expr):
						if not hasattr(expr, '_SymbolicValue__mnemonic'):
							return expr
						elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_IN and expr._SymbolicValue__operands[0] == loop_id and expr._SymbolicValue__operands[1] in erase_keys:
							return erase_loop_in(expr._SymbolicValue__operands[2])
						else:
							try:
								if isinstance(expr._SymbolicValue__operands, str):
									raise TypeError
								oo = iter(expr._SymbolicValue__operands)
							except TypeError:
								return expr
							else:
								return SymbolicValue(mnemonic=expr._SymbolicValue__mnemonic, type_=expr._SymbolicValue__type, length=expr._SymbolicValue__length, operands=[erase_loop_in(_sexpr) for _sexpr in oo])
					
					looped = {}
					for key in looped_keys:
						t, s = symbolize(final[key])
						looped[key] = t(SymbolicValue._loop_out(loop_id, key, erase_loop_in(SymbolicValue(s))))
				
				def add_call_id(expr):
					#print("add_call_id", loop_id, call_id)
					if not hasattr(expr, '_SymbolicValue__mnemonic'):
						return expr
					elif expr._SymbolicValue__mnemonic in (expr.Mnemonic.LOOP_OUT, expr.Mnemonic.LOOP_IN, expr.Mnemonic.LOOP_CNT) and expr._SymbolicValue__operands[0] == loop_id:
						v = SymbolicValue(mnemonic=expr._SymbolicValue__mnemonic, type_=expr._SymbolicValue__type, length=expr._SymbolicValue__length, operands=[add_call_id(_sexpr) for _sexpr in expr._SymbolicValue__operands])
						v._SymbolicValue__operands[0] += '_' + str(call_id)
						return v
					else:
						try:
							if isinstance(expr._SymbolicValue__operands, str):
								raise TypeError
							oo = iter(expr._SymbolicValue__operands)
						except TypeError:
							return expr
						else:
							return SymbolicValue(mnemonic=expr._SymbolicValue__mnemonic, type_=expr._SymbolicValue__type, length=expr._SymbolicValue__length, operands=[add_call_id(_sexpr) for _sexpr in oo])
				
				frame = inspect.stack()[1].frame
				frame.f_locals.update({_key:add_call_id(_value) for (_key, _value) in looped.items()})
				pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0))
				raise __Pass
			
			return new_fn
	
	else:
		def decorator(fn):
			return fn
	
	return decorator


class __Break(BaseException):
	pass


class __Continue(BaseException):
	pass


class __Pass(BaseException):
	pass


class Transformer(ast.NodeTransformer):
	def __init__(self, clsname, methname):
		self.clsname = clsname
		self.methname = methname
		self.in_for = False
		self.loop_no = 0
		self.target = []
		self.iter_ = []
		self.counter = []
		self.generator_args = []
		self.generator_cnt = 0
	
	def visit_Name(self, node):
		if node.id == '__target':
			if hasattr(self.target[-1], 'elts'):
				args = []
				for name in self.target[-1].elts:
					args.append(ast.Name(name.id, ast.Load()))
				return args
			else:
				return ast.Name(self.target[-1].id, ast.Load())
				return node
		elif node.id == '__iter':
			return self.iter_[-1]
		elif node.id == '__counter':
			return ast.Name(self.counter[-1], ast.Load())
		else:
			return node
	
	def visit_Attribute(self, node):
		if self.clsname and node.attr.startswith('__') and not node.attr.endswith('__'):
			node.attr = f'_{self.clsname}{node.attr}'
			return node
		else:
			return node
	
	def visit_GeneratorExp(self, node):
		n = self.generator_cnt
		self.generator_cnt += 1
		self.generator_args.append(node)
		return ast.parse(f'_generator_{self.clsname}_{self.methname}_{n}').body[0].value
		#return ast.parse(f'FieldList(SymbolicValue._list({ast.unparse(node)}))').body[0].value
	
	def visit_Expr(self, node):
		if isinstance(node.value, ast.Call):
			if hasattr(node.value.func, 'id'):
				if node.value.func.id == '__body':
					#print("body")
					#print(ast.unparse(self.body))
					return [self.visit(_stmt) for _stmt in self.body]
				elif node.value.func.id == '__orelse':
					return self.orelse
			args = []
			for arg in node.value.args:
				varg = self.visit(arg)
				if isinstance(varg, list):
					args.extend(varg)
				else:
					args.append(varg)
			node.value.args = args
		
		else:
			node.value = self.visit(node.value)
		
		return node
	
	def visit(self, node):
		node = super().visit(node)
		if self.generator_args and isinstance(node, ast.Return):
			exs = []
			for n, ge in enumerate(self.generator_args):
				#print(self.clsname, self.methname, "generator:", ast.unparse(ge))
				
				ncnt = self.generator_cnt - len(self.generator_args) + n
				generators = list(ge.generators)
				len_expr = '*'.join(f'len({ast.unparse(_comp.iter)})' for _comp in generators)
				
				exs.extend(ast.parse(f'''
_generator_{self.clsname}_{self.methname}_{ncnt} = SymbolicValue._listcomp({len_expr})
''').body)
				
				#if hasattr(generators[0].target, 'elts'):
				#	target_id = ', '.join(_name.id for _name in generators[0].target.elts)
				#else:
				#	target_id = generators[0].target.id
				
				body = ast.parse(f'''
_generator_{self.clsname}_{self.methname}_{ncnt}[__counter - 1] = symbolize({ast.unparse(ge.elt)})[1]
''').body
				for comp in generators:
					target = comp.target
					iter_ = comp.iter
					ifs = comp.ifs			
					body = [ast.For(target, iter_, body, [])]
				exs.extend(body)
			
			self.generator_args.clear()
			exs.append(node)
			#exs.append(ast.parse(f'__generator_{n}._free()').body[0])  # TODO: finally
			
			ret = []
			for stmt in exs:
				stmt = ast.fix_missing_locations(stmt)
				stmt = self.visit(stmt)
				if isinstance(stmt, list):
					ret.extend(stmt)
				else:
					ret.append(stmt)
			return ret
		
		elif isinstance(node, ast.Call):
			if hasattr(node.func, 'id'):
				if node.func.id == 'range':
					return ast.parse('SymbolicValue._range(' + ', '.join(ast.unparse(_arg) for _arg in node.args) + ')').body[0].value
				elif node.func.id == 'product':
					return ast.parse('SymbolicValue._product(' + ', '.join(ast.unparse(_arg.args[0]) for _arg in node.args) + ')').body[0].value
		
		return node
	
	def visit_Assign(self, node):
		if hasattr(node.targets[0], 'id') and node.targets[0].id == '__target':
			return ast.parse(f'{ast.unparse(self.target[-1])} = {ast.unparse(self.visit(node.value))}').body[0]
		else:
			node.targets = [self.visit(_target) for _target in node.targets]
			node.value = self.visit(node.value)
			return node
	
	def visit_Break(self, node):
		if self.in_for:
			return ast.parse('raise __Break').body[0]
		else:
			return node
	
	def visit_Continue(self, node):
		if self.in_for:
			return ast.parse('raise __Continue').body[0]
		else:
			return node
	
	def visit_arg(self, node):
		if node.arg == '__target':
			if hasattr(self.target[-1], 'elts'):
				args = []
				for name in self.target[-1].elts:
					args.append(ast.arg(name.id))
				return args
			else:
				node.arg = self.target[-1].id
				return node
		return node
	
	def visit_For(self, node):
		loop_no = self.loop_no
		self.loop_no += 1
		
		lineno = node.lineno
		col_offset = node.col_offset
		
		self.target.append(node.target)
		self.iter_.append(node.iter)
		self.counter.append(f'_counter_{self.clsname}_{self.methname}_{loop_no}')
		
		was_in_for = self.in_for
		self.in_for = True
		body = []
		for statement in node.body:
			r = self.visit(statement)
			if isinstance(r, list):
				body.extend(r)
			else:
				body.append(r)
		
		self.body = body
		def_loop = ast.parse(f'''
@__loop_body("{self.clsname}_{self.methname}_{loop_no}", __iter)
def __loop_{self.clsname}_{self.methname}_{loop_no}(__target, __call_id):
	__load_vars()
	try:
		__body()
	finally:
		__save_vars()
	raise __Pass
''')
		
		def_loop = self.visit(def_loop)
		
		orelse = []
		for statement in node.orelse:
			orelse.append(self.visit(statement))
		if orelse:
			self.orelse = orelse
		else:
			self.orelse = [ast.parse('pass').body[0]]
		self.in_for = False
		
		call_loop = ast.parse(f'''
_counter_{self.clsname}_{self.methname}_{loop_no} = SymbolicValue._loop_cnt("{self.clsname}_{self.methname}_{loop_no}", len(__iter))
while _counter_{self.clsname}_{self.methname}_{loop_no}._SymbolicValue__mnemonic == SymbolicValue.Mnemonic.LOOP_CNT:
	#print("unpack...")
	__target = __iter[_counter_{self.clsname}_{self.methname}_{loop_no}]
	#print("unpacked")
	_counter_{self.clsname}_{self.methname}_{loop_no} += 1
	try:
		return __loop_{self.clsname}_{self.methname}_{loop_no}(__target, hex(id(__iter))[2:])
	except __Break:
		break
	except __Continue:
		continue
	except __Pass:
		pass
else:
	__orelse()
''')
		
		call_loop = self.visit(call_loop)
		
		del self.target[-1], self.iter_[-1], self.counter[-1]
		
		self.in_for = was_in_for
		
		return def_loop.body + call_loop.body


def transform(fn, clsname=None):
	try:
		cls = fn.__self__
		if clsname is None:
			clsname = cls.__name__
		#fn = fn.__func__
	except AttributeError:
		cls = None
	
	source = 'if True:\n' + inspect.getsource(fn)
	orig_tree = ast.parse(source)
	mod_tree = Transformer(clsname, fn.__name__).visit(orig_tree)
	mod_tree = ast.fix_missing_locations(mod_tree)
	#print(ast.unparse(mod_tree))
	code = compile(mod_tree, '<string>', 'exec')
	globals_ = dict(globals())
	locals_ = {}
	exec(code, globals_, locals_)
	ft = locals_[fn.__name__]
	
	if cls is not None:
		nft = lambda *args: ft.__func__(cls, *args)
	else:
		nft = ft
	
	nft.__name__ = fn.__name__
	nft.__qualname__ = fn.__qualname__
	return nft


def substitute_expr(expr, subst_in, subst_out):
	if expr == subst_in:
		return subst_out
	
	if not hasattr(expr, '_SymbolicValue__mnemonic'):
		return expr
	
	try:
		if isinstance(expr._SymbolicValue__operands, str):
			raise TypeError
		oo = iter(expr._SymbolicValue__operands)
	except TypeError:
		return expr
	
	return SymbolicValue(expr._SymbolicValue__mnemonic, expr._SymbolicValue__type, expr._SymbolicValue__length, [substitute_expr(_operand, subst_in, subst_out) for _operand in oo])


def optimize_expr_single(expr):
	if not hasattr(expr, '_SymbolicValue__mnemonic'):
		return expr
	
	try:
		if isinstance(expr._SymbolicValue__operands, str):
			raise TypeError
		oo = iter(expr._SymbolicValue__operands)
	except TypeError:
		#return SymbolicValue(expr._SymbolicValue__mnemonic, expr._SymbolicValue__type, expr._SymbolicValue__length, expr._SymbolicValue__operands)
		return expr
	
	expr = SymbolicValue(expr._SymbolicValue__mnemonic, expr._SymbolicValue__type, expr._SymbolicValue__length, [optimize_expr_single(_operand) for _operand in oo])
	
	if expr._SymbolicValue__mnemonic == expr.Mnemonic.SUB and \
	    expr._SymbolicValue__operands[0]._SymbolicValue__mnemonic == expr.Mnemonic.ADD and \
	     expr._SymbolicValue__operands[1] == expr._SymbolicValue__operands[0]._SymbolicValue__operands[1]:
		return expr._SymbolicValue__operands[0]._SymbolicValue__operands[0]
	
	"Optimize some typical index operations."
	if expr._SymbolicValue__mnemonic == expr.Mnemonic.INDEX and \
	    expr._SymbolicValue__operands[0]._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_OUT and \
	     expr._SymbolicValue__operands[0]._SymbolicValue__operands[2]._SymbolicValue__mnemonic == expr.Mnemonic.STORE and \
	      expr._SymbolicValue__operands[0]._SymbolicValue__operands[2]._SymbolicValue__operands[0]._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_IN and \
	       expr._SymbolicValue__operands[0]._SymbolicValue__operands[2]._SymbolicValue__operands[1]._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_CNT and \
	        expr._SymbolicValue__operands[0]._SymbolicValue__operands[0] == \
	         expr._SymbolicValue__operands[0]._SymbolicValue__operands[2]._SymbolicValue__operands[0]._SymbolicValue__operands[0] == \
	          expr._SymbolicValue__operands[0]._SymbolicValue__operands[2]._SymbolicValue__operands[1]._SymbolicValue__operands[0] and \
	           expr._SymbolicValue__operands[0]._SymbolicValue__operands[1] == \
	            expr._SymbolicValue__operands[0]._SymbolicValue__operands[2]._SymbolicValue__operands[0]._SymbolicValue__operands[1]:
		index_inside = expr._SymbolicValue__operands[0]._SymbolicValue__operands[2]._SymbolicValue__operands[1]
		index_outside = expr._SymbolicValue__operands[1]
		loop_id, var_name = expr._SymbolicValue__operands[0]._SymbolicValue__operands[0:2]
		assert index_inside._SymbolicValue__operands[1] == index_outside._SymbolicValue__operands[1]
		body = expr._SymbolicValue__operands[0]._SymbolicValue__operands[2]._SymbolicValue__operands[2]
		return substitute_expr(body, index_inside, index_outside)
	
	return expr


def optimize_expr(expr):
	prev = expr
	expr = optimize_expr_single(expr)
	while prev != expr:
		prev = expr
		expr = optimize_expr_single(expr)
	
	return expr


class SymbolicArray:
	def __init__(self, values, sizes=None, types=None):
		try:
			self.__values = values.__values
			self.__sizes = values.__sizes
			self.__types = values.__types
		except AttributeError:
			if isinstance(values, SymbolicValue):
				self.__values = values
			else:
				tv = [symbolize(_v) for _v in values]
				t, v = zip(*tv)
				self.__values = SymbolicValue(v)
				if types is None:
					types = [t[0]]
			
			if sizes is not None:
				self.__sizes = sizes
			else:
				self.__sizes = [None]
			
			if types is not None:
				self.__types = types
			else:
				assert self.__values[0].__class__ != SymbolicValue
				self.__types = [self.__values[0].__class__]
	
	def __getnewargs__(self):
		return self.__values, self.__sizes, self.__types
	
	def __getitem__(self, index):
		if hasattr(index, 'start') and hasattr(index, 'stop'):
			raise NotImplementedError("Imlpement slicing of SymbolicArray")
		else:
			if len(self.__types) == 1:
				return self.__types[0](self.__values[index])
			else:
				#d = 1
				#for s in self.__sizes[:-1]:
				#	d *= s
				#assert len(self.__values) % d == 0
				l = len(self.__values) // self.__sizes[0]
				return self.__types[0](self.__class__(self.__values[index * l : (index + 1) * l], self.__sizes[1:], self.__types[1:]))
	
	def __len__(self):
		if self.__sizes[0] is None:
			return len(self.__values)
		else:
			return self.__sizes[0]

SymbolicArray.Array = SymbolicArray


class SymbolicTable:
	def __init__(self, values, ksize=None, sizes=None, types=None, Array=None):
		try:
			self.__values = values.__values
			self.__ksize = values.__ksize
			self.__sizes = values.__sizes
			self.__types = values.__types
			self.Array = values.Array
		except AttributeError:
			if isinstance(values, SymbolicValue):
				self.__values = values
			else:
				self.__values = dict(values)
			
			if ksize is not None:
				self.__ksize = ksize
			else:
				ksize = None
				for key in self.__values.keys():
					if ksize is None:
						ksize = tuple(key)
					else:
						ksize = [max(_a, _b) for (_a, _b) in zip(ksize, key)]
				self.__ksize = ksize
			
			if sizes is not None:
				self.__sizes = sizes
			else:
				self.__sizes = [None]
			
			if types is not None:
				self.__types = types
			else:
				assert self.__values[0].__class__ != SymbolicValue, f"{self.__values}[0] should not be SymbolicValue"
				self.__types = [self.__values[0].__class__]
		
		if Array is not None:
			self.Array = Array
	
	def __getnewargs__(self):
		return self.__values, self.__ksize, self.__sizes, self.__types
	
	def __getitem__(self, index):
		if hasattr(index, 'start') and hasattr(index, 'stop'):
			raise NotImplementedError
		else:
			if len(self.__types) == 1:
				return self.__types[0](self.__values[index])
			else:
				offset = index[0].__class__(0)
				for i, s in zip(index, self.__ksize):
					if not 0 <= i < s:
						raise KeyError(f"Index {tuple(index)} out of bounds: {tuple(self.__ksize)}")
					offset *= s
					offset += i
				
				d = 1
				for s in self.__ksize:
					d *= s
				
				assert len(self.__values) % d == 0
				l = len(self.__values) // d
				
				if self.__sizes[0] is None:
					return self.__types[0](self.__values[offset])
				elif not isinstance(self.__sizes[0], tuple):
					return self.__types[0](self.Array(self.__values[offset * l : (offset + 1) * l], self.__sizes, self.__types[1:]))
				else:
					return self.__types[0](self.__class__(self.__values[offset * l : (offset + 1) * l], self.__sizes[0], self.__sizes[1:], self.__types[1:]))
	
	def keys(self):
		yield from product(*[range(_k) for _k in self.__ksize])

SymbolicTable.Array = SymbolicArray
SymbolicTable.Table = SymbolicTable

