#!/usr/bin/python3


from enum import Enum
from ctypes import CFUNCTYPE, c_uint8, c_int16, POINTER
from ctypes import py_object, c_int, pythonapi
from llvmlite.ir import Module, IntType, ArrayType, Constant, GlobalVariable, FunctionType, Function, IRBuilder
from llvmlite.ir._utils import DuplicatedNameError
from llvmlite.binding import initialize, initialize_native_target, initialize_native_asmprinter, parse_assembly, create_mcjit_compiler, Target, get_process_triple
from collections import defaultdict
from collections.abc import Iterable
from itertools import chain, zip_longest
import ast, inspect
from functools import cmp_to_key


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
		
		if frozenset({self.__type, other.__type}) == frozenset({self.Type.UINT}):
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
		
		r = self.__class__._if(self >= self.__class__(0), self, -self)
		return self.__class__(r.__mnemonic, self.Type.UINT, r.__length, r.__operands)
	
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


def build_array(module, name, int_t, array):
	array_t = ArrayType(int_t, len(array._SymbolicValue__operands))
	result = GlobalVariable(module, array_t, name)
	result.initializer = array_t([int_t(_n._SymbolicValue__operands) for _n in array._SymbolicValue__operands])
	result.global_constant = True


#def find_loop_in(expr):
#	if not hasattr(expr, '_SymbolicValue__mnemonic'):
#		return
#	elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_IN:
#		yield expr
#	elif isinstance(expr._SymbolicValue__operands, list):
#		for operand in expr._SymbolicValue__operands:
#			yield from find_loop_in(operand)


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


def build_function(module, name, args_t, return_t, int_t, size_t, expr):
	"""
	module - llvmlite module
	name - function name
	args_t - list of function arg types
	return_t - function return type
	int_t - type for arithmetics, should be 2 times bigger than args and return
	size_t - type for list indices, should be bigger than the biggest array and number of loop iterations, plus 1 sign bit
	expr - SymbolicValue, function body
	
	int_t, size_t and expr may be None, in that case a declaration will be created
	"""
	
	function_t = FunctionType(return_t, args_t)
	try:
		function = Function(module, function_t, name)
	except DuplicatedNameError:
		function = module.get_global(name)
	assert function.type.pointee == function_t, f"{function.type} == {function_t}"
	
	if expr is None:
		assert function.is_declaration
		return
	
	def find_loop_in(expr):
		if not hasattr(expr, '_SymbolicValue__mnemonic'):
			return
		
		if expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_IN:
			yield expr
		
		try:
			oo = iter(expr._SymbolicValue__operands)
		except TypeError:
			pass
		else:
			for sexpr in oo:
				yield from find_loop_in(sexpr)
	
	def convert_args(args, ops, builder):
		if args[0].type != args[1].type:
			if args[0].type.width > args[1].type.width:
				if ops[1]._SymbolicValue__type == expr.Type.UINT:
					args[1] = builder.zext(args[1], args[0].type)
				elif ops[1]._SymbolicValue__type == expr.Type.INT:
					args[1] = builder.sext(args[1], args[0].type)
				else:
					raise RuntimeError
			
			elif args[0].type.width < args[1].type.width:
				if ops[0]._SymbolicValue__type == expr.Type.UINT:
					args[0] = builder.zext(args[0], args[1].type)
				elif ops[0]._SymbolicValue__type == expr.Type.INT:
					args[0] = builder.sext(args[0], args[1].type)
				else:
					raise RuntimeError
			
			else:
				raise RuntimeError
	
	def assemble(expr, builder):
		#print("assemble", builder.block.name, expr._SymbolicValue__mnemonic.name)
		if expr._SymbolicValue__mnemonic == expr.Mnemonic.CALL or (isinstance(expr._SymbolicValue__operands, Iterable) and not isinstance(expr._SymbolicValue__operands, str)):
			if expr._SymbolicValue__mnemonic == expr.Mnemonic.IF:
				c, yes, no = expr._SymbolicValue__operands
				
				if isinstance(c, SymbolicValue) and c._SymbolicValue__mnemonic != expr.Mnemonic.CONST:
					c, c_builder = assemble(c, builder)
					if c.type != bool_t:
						c = c_builder.icmp_signed('!=', c, c.type(0))
					
					yes_builder_enter = IRBuilder(function.append_basic_block())
					yes_builder_enter.comment("yes case")
					yes_r, yes_builder_exit = assemble(yes, yes_builder_enter)
					no_builder_enter = IRBuilder(function.append_basic_block())
					no_builder_enter.comment("no case")
					no_r, no_builder_exit = assemble(no, no_builder_enter)
					
					assert yes_r.type == no_r.type
					
					c_builder.comment("if?")
					c_builder.cbranch(c, yes_builder_enter.block, no_builder_enter.block)
					r_builder = IRBuilder(function.append_basic_block())
					yes_builder_exit.comment("join after conditional (from yes)")
					yes_builder_exit.branch(r_builder.block)
					no_builder_exit.comment("join after conditional (from no)")
					no_builder_exit.branch(r_builder.block)
					
					phi = r_builder.phi(yes_r.type)
					phi.add_incoming(yes_r, yes_builder_exit.block)
					phi.add_incoming(no_r, no_builder_exit.block)
					return phi, r_builder
				else:
					raise NotImplementedError
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_CNT:
				loop_id, iter_num = expr._SymbolicValue__operands
				
				if (loop_id, '__counter') in loop_var:
					var, _, _ = loop_var[loop_id, '__counter']
					return var, builder
				
				enter_builder = loop_enter[loop_id]
				enter_builder.comment(f"loop {loop_id} counter")
				var = enter_builder.phi(size_t)
				#var.add_incoming(size_t(0), old_builder.block)
				
				loop_var[loop_id, '__counter'] = var, 0, iter_num
				
				return var, builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_IN:
				loop_no, var_name, in_expr = expr._SymbolicValue__operands
				
				if loop_no not in loop_before: # LOOP_IN outside corresponding LOOP_OUT (invariant)
					return assemble(in_expr, builder) # return initial value unchanged
				
				assert loop_no in loop_before
				assert loop_no in loop_enter
				assert loop_no in loop_begin
				assert loop_no in loop_body
				assert loop_no in loop_exit
				assert loop_no in loop_after
				
				if (loop_no, var_name) in loop_var:
					var, in_result, out_result = loop_var[loop_no, var_name]
				else:
					var = in_result = out_result = None
				
				if in_result is None:
					before_builder = loop_before[loop_no]
					in_result, before_builder = assemble(in_expr, before_builder) # calculate initial value in the block before the loop
					loop_before[loop_no] = before_builder
					#print(f"created in var {var_name}")
				
				if var is None:
					if expr._SymbolicValue__length is not None: # array
						var = in_result
					else: # scalar
						enter_builder = loop_enter[loop_no]
						enter_builder.comment(f"loop {loop_no} variable {var_name}")
						var = enter_builder.phi(in_result.type)			
				
				loop_var[loop_no, var_name] = var, in_result, out_result
				
				#print(f"returned in var {var_name}", in_result, out_result)
				return var, builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_OUT:
				loop_no, var_name, out_expr = expr._SymbolicValue__operands
				
				arg_builder = builder
				del builder
				
				if loop_no in loop_before:
					before_builder = loop_before[loop_no]
					loop_first_time = False
				else:
					before_builder = loop_before[loop_no] = IRBuilder(function.append_basic_block())
					before_builder.comment(f"before loop {loop_no}")
					loop_first_time = True
				
				if loop_no in loop_enter:
					enter_builder = loop_enter[loop_no]
				else:
					enter_builder = loop_enter[loop_no] = IRBuilder(function.append_basic_block())
					enter_builder.comment(f"enter loop {loop_no}")
				
				if loop_no in loop_body:
					assert loop_no in loop_begin
					body_builder = loop_body[loop_no]
				else:
					body_builder = loop_body[loop_no] = loop_begin[loop_no] = IRBuilder(function.append_basic_block())
					body_builder.comment(f"begin loop {loop_no}")
				
				if loop_no in loop_exit:
					exit_builder = loop_exit[loop_no]
				else:
					exit_builder = loop_exit[loop_no] = IRBuilder(function.append_basic_block())
					exit_builder.comment(f"exit loop {loop_no}")
				
				if loop_no in loop_after:
					after_builder = loop_after[loop_no]
				else:
					after_builder = loop_after[loop_no] = IRBuilder(function.append_basic_block())
					after_builder.comment(f"after loop {loop_no}")
				
				if loop_first_time:
					arg_builder.comment(f"execute loop {loop_no}")
					arg_builder.branch(before_builder.block)
					
					ret_builder = after_builder
					ret_builder.comment(f"return from loop {loop_no}")
					#print("execute loop", loop_no, "from", arg_builder.block.name, "returning to", ret_builder.block.name)
				else:
					ret_builder = arg_builder
				
				if (loop_no, var_name) in loop_var:
					var, in_result, out_result = loop_var[loop_no, var_name]
				else:
					var = in_result = out_result = None
				
				if out_result is None:
					#print("{", loop_no, var_name, body_builder.block.name)
					out_result, body_builder = assemble(out_expr, body_builder) # calculate result of loop variable
					#print("}", loop_no, var_name, body_builder.block.name)
					loop_body[loop_no] = body_builder
					#print(f"created out var {var_name}")
				
				if (loop_no, var_name) in loop_var: # in var might have been created through out_expr
					var, in_result, _ = loop_var[loop_no, var_name]
				
				if var is None:
					enter_builder.comment(f"loop {loop_no} variable {var_name}")
					var = enter_builder.phi(out_result.type)
				
				loop_var[loop_no, var_name] = var, in_result, out_result
				
				#print(f" return from loop var {var_name}", loop_first_time, arg_builder.block.name, ret_builder.block.name)
				return var, ret_builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.CALL:
				fn = expr._SymbolicValue__operands[0]
				if isinstance(fn, SymbolicValue):
					fn, builder = assemble(fn, builder)
				
				def type_listcomp(expr, lltype):
					if not hasattr(expr, '_SymbolicValue__mnemonic'):
						return expr
					elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LISTCOMP:
						return expr.__class__(expr.Mnemonic.LISTCOMP, expr._SymbolicValue__type, expr._SymbolicValue__length, lltype)
					else:
						try:
							if isinstance(expr._SymbolicValue__operands, str):
								raise TypeError
							oo = iter(expr._SymbolicValue__operands)
						except TypeError:
							return SymbolicValue(mnemonic=expr._SymbolicValue__mnemonic, type_=expr._SymbolicValue__type, length=expr._SymbolicValue__length, operands=type_listcomp(expr._SymbolicValue__operands, lltype))
						else:
							return SymbolicValue(mnemonic=expr._SymbolicValue__mnemonic, type_=expr._SymbolicValue__type, length=expr._SymbolicValue__length, operands=[type_listcomp(_sexpr, lltype) for _sexpr in oo])
				
				args = []
				for e, tt in zip(expr._SymbolicValue__operands[1:], fn.type.pointee.args):
					if hasattr(tt, 'pointee') and e._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_OUT and e._SymbolicValue__length is not None:
						e = type_listcomp(e, tt.pointee.element)
					
					if isinstance(e, SymbolicValue):
						r, builder = assemble(e, builder) # function argument
					else:
						r = e
					
					args.append(r)
				
				tr_args = []
				for a, tt in zip(args, fn.type.pointee.args):
					if isinstance(a, list):
						alloc_builder.comment("list arg")
						l = alloc_builder.alloca(tt.pointee)
						for n, el in enumerate(a):
							p = builder.gep(l, [size_t(0), size_t(n)])
							v = builder.trunc(el, tt.pointee.element)
							builder.store(v, p)
						a = l
					elif a.type != tt:
						a = builder.trunc(a, tt)
					tr_args.append(a)
				
				r = builder.call(fn, tr_args)
				if expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.INT:
					r = builder.sext(r, int_t)
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.UINT:
					r = builder.zext(r, int_t)
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
				
				return r, builder
			
			else:
				args = []
				for e in expr._SymbolicValue__operands:
					if isinstance(e, SymbolicValue):
						r, builder = assemble(e, builder) # generic value
					else:
						r = e
					
					assert not isinstance(r, list), str(e)
					
					args.append(r)
			
			if expr._SymbolicValue__mnemonic == expr.Mnemonic.CONST:
				if expr._SymbolicValue__type == expr.Type.LIST_INT or expr._SymbolicValue__type == expr.Type.LIST_UINT:
					assert len(expr._SymbolicValue__operands) == len(args)
					at = ArrayType(int_t, expr._SymbolicValue__length)
					alloc_builder.comment("const list")
					ar = alloc_builder.alloca(at)
					for n, v in enumerate(args):
						p = builder.gep(ar, [size_t(0), size_t(n)])
						if v.type == int_t:
							cv = v
						else:
							cv = builder.zext(v, int_t)
						builder.store(cv, p)
					return ar, builder
				else:
					raise NotImplementedError(str(expr._SymbolicValue__type))
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.INDEX:
				p = builder.gep(args[0], [size_t(0), args[1]])
				r = builder.load(p)
				
				if expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.LIST_UINT:
					q = builder.zext(r, int_t)
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.LIST_INT:
					#builder.comment("signed int array element")
					q = builder.sext(r, int_t)
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
				
				return q, builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.XOR:
				convert_args(args, expr._SymbolicValue__operands, builder)
				return builder.xor(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.ADD:
				convert_args(args, expr._SymbolicValue__operands, builder)
				return builder.add(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.SUB:
				convert_args(args, expr._SymbolicValue__operands, builder)
				return builder.sub(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.MUL:
				convert_args(args, expr._SymbolicValue__operands, builder)
				return builder.mul(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.POW:
				try:
					if args[0].constant != 2:
						raise NotImplementedError("Only power of 2 is supported.")
				except AttributeError:
					raise NotImplementedError("Only constant base powe is supported.")
				
				return builder.shl(args[0].type(1), builder.trunc(args[1], args[0].type)), builder # power is shift left
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.GE:
				return builder.icmp_signed('>=', args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.EQ:
				return builder.icmp_signed('==', args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.FLOORDIV:
				if expr._SymbolicValue__operands[1]._SymbolicValue__type != expr.Type.UINT:
					raise NotImplementedError(str(expr._SymbolicValue__operands[1]._SymbolicValue__type))
				
				if expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.INT:
					convert_args(args, expr._SymbolicValue__operands, builder)
					return builder.udiv(args[0], args[1]), builder # udiv in Python semantics
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.UINT:
					convert_args(args, expr._SymbolicValue__operands, builder)
					return builder.udiv(args[0], args[1]), builder
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.MOD:
				if expr._SymbolicValue__operands[1]._SymbolicValue__type != expr.Type.UINT:
					raise NotImplementedError(str(expr._SymbolicValue__operands[1]._SymbolicValue__type))
				
				if expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.INT:
					convert_args(args, expr._SymbolicValue__operands, builder)
					return builder.urem(args[0], args[1]), builder # urem in Python semantics
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.UINT:
					convert_args(args, expr._SymbolicValue__operands, builder)
					return builder.urem(args[0], args[1]), builder
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.STORE:
				p = builder.gep(args[0], [size_t(0), args[1]])
				v = builder.trunc(args[2], args[0].type.pointee.element)
				builder.store(v, p)
				return args[0], builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.SLICE:
				#i = builder.mul(args[0], args[0].type(expr._SymbolicValue__length))
				p = builder.gep(args[1], [size_t(0), args[0]])
				v = builder.bitcast(p, ArrayType(args[1].type.pointee.element, expr._SymbolicValue__length).as_pointer())
				return v, builder
			
			else:
				raise NotImplementedError(str(expr))
		
		else:
			if expr._SymbolicValue__mnemonic == expr.Mnemonic.CONST:
				return int_t(expr._SymbolicValue__operands), builder
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.ARG:
				a = function.args[expr._SymbolicValue__operands]
				if expr._SymbolicValue__type == expr.Type.UINT:
					r = builder.zext(a, int_t)
				elif expr._SymbolicValue__type == expr.Type.INT:
					#builder.comment("signed int formal arg")
					r = builder.sext(a, int_t)
				elif expr._SymbolicValue__type == expr.Type.LIST_INT or expr._SymbolicValue__type == expr.Type.LIST_UINT:
					r = a
				else:
					raise NotImplementedError(str(expr._SymbolicValue__type))
				return r, builder
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.PTR:
				return module.get_global(expr._SymbolicValue__operands), builder
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.FUN:
				return module.get_global(expr._SymbolicValue__operands), builder
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LISTCOMP:
				lltype = expr._SymbolicValue__operands
				#assert lltype is not None
				#FIXME
				if lltype is None:
					lltype = byte_t
				assert isinstance(expr._SymbolicValue__length, int)
				alloc_builder.comment("listcomp")
				lc = alloc_builder.alloca(ArrayType(lltype, expr._SymbolicValue__length))
				for lcn in range(expr._SymbolicValue__length):
					p = builder.gep(lc, [size_t(0), size_t(lcn)])
					builder.store(lltype(0), p)
				return lc, builder
			
			else:
				raise NotImplementedError(str(expr))
	
	loop_var = {} # loop variables
	loop_before = {} # block before the loop, calculate initial values
	loop_enter = {} # loop head, merge initial and update values, increment counter, jump to begin or exit block
	loop_begin = {} # loop start, first block in loop body
	loop_body = {} # current (last) block in loop body
	loop_exit = {} # loop exit block; TODO: implement exceptions
	loop_after = {} # block after the loop
	
	alloc_builder = IRBuilder(function.append_basic_block()) # block with table allocations
	
	begin_builder = builder = IRBuilder(function.append_basic_block()) # first code block in the function
	builder.comment(f"begin function {name}")
	result, builder = assemble(expr, builder) # build function result
	if isinstance(result, list):
		assert return_t == args_t[-1]
		assert len(result) == return_t.pointee.count, f"{function_t} ;;; {function.type}"
		r = function.args[len(args_t) - 1]
		for n, val in enumerate(result):
			p = builder.gep(r, [size_t(0), size_t(n)])
			v = builder.trunc(val, return_t.pointee.element)
			builder.store(v, p)
	elif hasattr(return_t, 'pointee') and hasattr(return_t.pointee, 'element'):
		assert return_t == args_t[-1]
		assert result.type == return_t
		r = function.args[len(args_t) - 1]
		for n in range(return_t.pointee.count):
			pr = builder.gep(r, [size_t(0), size_t(n)])
			pv = builder.gep(result, [size_t(0), size_t(n)])
			v = builder.load(pv)
			builder.store(v, pr)
	else:
		r = builder.trunc(result, return_t)
	
	builder.ret(r)
	builder.comment(f"end function {name}")
	
	alloc_builder.branch(begin_builder.block)

	for loop_no, builder in loop_before.items():
		builder.branch(loop_enter[loop_no].block)
	
	for loop_no, builder in loop_body.items():
		var, _, _ = loop_var[loop_no, '__counter']
		var_plus_1 = builder.add(var, size_t(1))
		builder.branch(loop_enter[loop_no].block)
		builder.comment(f"end loop {loop_no}")
		var.add_incoming(size_t(0), loop_before[loop_no].block)
		var.add_incoming(var_plus_1, builder.block)
	
	for loop_no, builder in loop_enter.items():
		var, _, iter_num = loop_var[loop_no, '__counter']
		builder.comment(f"loop {loop_no} iteration limit {iter_num}")
		iter_num = size_t(iter_num)
		c = builder.icmp_signed('<', var, iter_num)
		builder.cbranch(c, loop_begin[loop_no].block, loop_exit[loop_no].block)
	
	for loop_no, builder in loop_exit.items():
		builder.branch(loop_after[loop_no].block)
	
	for (loop_no, var_name), (var, in_result, out_result) in loop_var.items():
		if var_name == '__counter': continue
		if hasattr(var, 'add_incoming'):
			#print(var_name, in_result, out_result)
			var.add_incoming(in_result, loop_before[loop_no].block)
			var.add_incoming(out_result, loop_body[loop_no].block)


bool_t = IntType(1)
byte_t = IntType(8)
short_t = IntType(16)
long_t = IntType(32)


def optimize(Field):
	module = Module()
	
	OptimizedField = type(Field.__name__, (Field,), {})
	OptimizedLinear = type('Linear', (Linear,), {})
	OptimizedQuadratic = type('Quadratic', (Quadratic,), {})
	OptimizedLinearCircuit = type('LinearCircuit', (LinearCircuit,), {})
	OptimizedQuadraticCircuit = type('QuadraticCircuit', (QuadraticCircuit,), {})
	
	build_array(module, 'Field.exponent', byte_t, SymbolicValue(OptimizedField.exponent))
	build_array(module, 'Field.logarithm', byte_t, SymbolicValue(OptimizedField.logarithm))
	
	OptimizedField.exponent = SymbolicValue._ptr_list_uint('Field.exponent', 256)
	OptimizedField.logarithm = SymbolicValue._ptr_list_uint('Field.logarithm', 256)
	
	trees = open('trees.txt', 'w')
	
	field_sum_types = set()
	orig_field_sum = OptimizedField.sum
	py_field_sum = transform(OptimizedField.sum, 'BinaryGalois')
	#py_field_sum = Field.sum
	def field_sum_capture(l):
		if not isinstance(l, SymbolicValue):
			l = symbolize(l)[1]
		
		if not isinstance(l, SymbolicValue):
			tl = [symbolize(_a) for _a in l]
			t, l = zip(*tl)
		
		if len(l) not in field_sum_types:
			field_sum_types.add(len(l))
			build_function(module, f'Field.sum_{len(l)}', [ArrayType(byte_t, len(l)).as_pointer()], byte_t, None, None, None)
		return SymbolicValue._fun_uint(f'Field.sum_{len(l)}')(l)
	#Field.sum = field_sum_capture
	OptimizedField.sum = lambda _l: OptimizedField(py_field_sum(SymbolicArray(symbolize(_l)[1], [None], [OptimizedField])))
	
	print("optimizing multiplication")
	body = optimize_expr(symbolize(trace(transform(OptimizedField.__mul__, 'BinaryGalois'), [OptimizedField(SymbolicValue._arg_uint(0)), OptimizedField(SymbolicValue._arg_uint(1))]))[1])
	print('Field.__mul__', file=trees)
	body._print_tree(file=trees)
	print(file=trees)
	build_function(module, 'Field.__mul__', [byte_t, byte_t], byte_t, short_t, long_t, body)
	OptimizedField.__mul__ = lambda _a, _b: OptimizedField(SymbolicValue._fun_uint('Field.__mul__')(symbolize(_a)[1], symbolize(_b)[1]))
	
	print("optimizing exponentiation")
	body = optimize_expr(symbolize(trace(transform(OptimizedField.__pow__, 'BinaryGalois'), [OptimizedField(SymbolicValue._arg_uint(0)), SymbolicValue._arg_int(1)]))[1])
	print('Field.__pow__', file=trees)
	body._print_tree(file=trees)
	print(file=trees)
	build_function(module, 'Field.__pow__', [byte_t, short_t], byte_t, short_t, long_t, body)
	OptimizedField.__pow__ = lambda _a, _b: OptimizedField(SymbolicValue._fun_uint('Field.__pow__')(symbolize(_a)[1], symbolize(_b)[1]))
	
	print("optimizing linear")
	py_linear_call = transform(OptimizedLinear.__call__, 'Linear')
	body = optimize_expr(symbolize(trace(py_linear_call, [OptimizedLinear(SymbolicArray(SymbolicValue._arg_list_uint(0, OptimizedField.field_power), [None], [OptimizedField])), OptimizedField(SymbolicValue._arg_uint(1))]))[1])
	print('Linear.__call__', file=trees)
	body._print_tree(file=trees)
	print(file=trees)
	build_function(module, 'Linear.__call__', [ArrayType(byte_t, OptimizedField.field_power).as_pointer(), byte_t], byte_t, short_t, long_t, body)
	OptimizedLinear.__call__ = lambda _l, _f: OptimizedField(py_linear_call(_l, OptimizedField(symbolize(_f)[1])))
	
	print("optimizing quadratic")
	body = optimize_expr(symbolize(trace(transform(OptimizedQuadratic.__call__, 'Quadratic'), [OptimizedQuadratic(SymbolicArray(SymbolicValue._arg_list_uint(0, OptimizedField.field_power**2), [OptimizedField.field_power, None], [OptimizedLinear, OptimizedField])), OptimizedField(SymbolicValue._arg_uint(1)), OptimizedField(SymbolicValue._arg_uint(2))]))[1])
	print('Quadratic.__call__', file=trees)
	body._print_tree(file=trees)
	print(file=trees)
	build_function(module, 'Quadratic.__call__', [ArrayType(byte_t, OptimizedField.field_power**2).as_pointer(), byte_t, byte_t], byte_t, short_t, long_t, body)
	OptimizedQuadratic.__call__ = lambda _q, _f1, _f2: OptimizedField(SymbolicValue._fun_uint('Quadratic.__call__')(symbolize(_q)[1], symbolize(_f1)[1], symbolize(_f2)[1]))
	
	print("optimizing linear circuit")
	linearcircuit_call_types = set()
	orig_linearcircuit_call = OptimizedLinearCircuit.__call__
	py_linearcircuit_call = OptimizedLinearCircuit.__call__
	def linearcircuit_call_capture(lc, iv):
		if not isinstance(lc, SymbolicValue):
			lc = symbolize(lc)[1]
			#lc = list(chain.from_iterable((SymbolicValue(lc[_o, _i].linear_coefficient(_k) for _k in range(OptimizedField.field_power))) for _o, _i in product(range(lc.output_size), range(lc.input_size))))
		
		if not isinstance(iv, SymbolicValue):
			iv = symbolize(iv)[1]
		
		len_lc = len(lc) // OptimizedField.field_power
		len_iv = len(iv)
		assert len_lc % len_iv == 0, f"{len_lc}, {len_iv}"
		len_ov = len_lc // len_iv
		
		if (len_ov, len_iv) not in linearcircuit_call_types:
			linearcircuit_call_types.add((len_ov, len_iv))
			#build_function(module, f'LinearCircuit.__call__{len_ov}_{len_iv}', [ArrayType(byte_t, len_lc * OptimizedField.field_power).as_pointer(), ArrayType(byte_t, len_iv).as_pointer(), ArrayType(byte_t, len_ov).as_pointer()], ArrayType(byte_t, len_ov).as_pointer(), None, None, None)
		return SymbolicValue._fun_uint(f'LinearCircuit.__call__{len_ov}_{len_iv}')(lc, iv)
	OptimizedLinearCircuit.__call__ = linearcircuit_call_capture
	
	for output_size, input_size in [(4, 12), (8, 12), (8, 20), (12, 20)]:
		lc = OptimizedLinearCircuit(SymbolicTable(SymbolicValue._arg_list_uint(0, OptimizedField.field_power * output_size * input_size), [output_size, input_size], [OptimizedField.field_power, None], [OptimizedLinear, OptimizedField]))
		iv = Vector(SymbolicArray(SymbolicValue._arg_list_uint(1, input_size), [None], [OptimizedField]))
		tr = lc(iv)
	
	#print("optimizing quadratic circuit")
	quadraticcircuit_call_types = set()
	orig_quadraticcircuit_call = OptimizedQuadraticCircuit.__call__
	py_quadraticcircuit_call = OptimizedQuadraticCircuit.__call__
	def quadraticcircuit_call_capture(qc, iv):
		if not isinstance(qc, SymbolicValue):
			qc = symbolize(qc)[1]
		
		if not isinstance(iv, SymbolicValue):
			iv = symbolize(iv)[1]
		
		assert isinstance(qc, SymbolicValue), type(qc).__name__
		
		len_qc = len(qc) // OptimizedField.field_power**2
		len_iv = len(iv)
		assert len_qc % len_iv**2 == 0, f"{len_qc}, {len_iv}"
		len_ov = len_qc // len_iv**2
		
		assert len(qc) == len(iv)**2 * len_ov * OptimizedField.field_power**2
		
		if (len_ov, len_iv) not in quadraticcircuit_call_types:
			quadraticcircuit_call_types.add((len_ov, len_iv))
			#build_function(module, f'QuadraticCircuit.__call__{len_ov}_{len_iv}', [ArrayType(byte_t, len_lc * OptimizedField.field_power).as_pointer(), ArrayType(byte_t, len_iv).as_pointer(), ArrayType(byte_t, len_ov).as_pointer()], ArrayType(byte_t, len_ov).as_pointer(), None, None, None)
		return SymbolicValue._fun_uint(f'QuadraticCircuit.__call__{len_ov}_{len_iv}')(qc, iv)
	OptimizedQuadraticCircuit.__call__ = quadraticcircuit_call_capture
	
	for output_size, input_size in [(8, 12), (4, 12), (1, 17), (16, 17)]:
		qc = OptimizedQuadraticCircuit(SymbolicTable(SymbolicValue._arg_list_uint(0, OptimizedField.field_power**2 * output_size * input_size**2), [output_size, input_size, input_size], [OptimizedField.field_power, OptimizedField.field_power, None], [OptimizedQuadratic, OptimizedLinear, OptimizedField]))
		iv = Vector(SymbolicArray(SymbolicValue._arg_list_uint(1, input_size), [None], [OptimizedField]))
		tr = qc(iv)
	
	#OptimizedField_sum_types.add(20)
	#OptimizedField_sum_types.add(12)
	#field_sum_types.add(144)
	#field_sum_types.add(289)
	#print("types:", field_sum_types, linearcircuit_call_types)
	
	'''
	for l in field_sum_types:
		body = symbolize(trace(py_field_sum, [SymbolicArray(SymbolicValue._arg_list_uint(0, l), [None], [OptimizedField])]))[1]
		build_function(module, f'Field.sum_{l}', [ArrayType(byte_t, l).as_pointer()], byte_t, short_t, long_t, body)
	'''
	
	for output_size, input_size in linearcircuit_call_types:
		lc = OptimizedLinearCircuit(SymbolicTable(SymbolicValue._arg_list_uint(0, OptimizedField.field_power * output_size * input_size), [output_size, input_size], [OptimizedField.field_power, None], [OptimizedLinear, OptimizedField]))
		assert lc.output_size == output_size
		assert lc.input_size == input_size
		iv = Vector(SymbolicArray(SymbolicValue._arg_list_uint(1, input_size), [None], [OptimizedField]))
		body = optimize_expr(symbolize(trace(transform(py_linearcircuit_call, 'LinearCircuit'), [lc, iv]))[1])
		print(f'LinearCircuit.__call__{output_size}_{input_size}', file=trees)
		body._print_tree(file=trees)
		print(file=trees)
		build_function(module, f'LinearCircuit.__call__{output_size}_{input_size}', [ArrayType(byte_t, input_size * output_size * OptimizedField.field_power).as_pointer(), ArrayType(byte_t, input_size).as_pointer(), ArrayType(byte_t, output_size).as_pointer()], ArrayType(byte_t, output_size).as_pointer(), short_t, long_t, body)
	
	for output_size, input_size in quadraticcircuit_call_types:
		qc = OptimizedQuadraticCircuit(SymbolicTable(SymbolicValue._arg_list_uint(0, OptimizedField.field_power**2 * output_size * input_size**2), [output_size, input_size, input_size], [OptimizedField.field_power, OptimizedField.field_power, None], [OptimizedQuadratic, OptimizedLinear, OptimizedField]))
		assert qc.output_size == output_size
		assert qc.input_size == input_size
		iv = Vector(SymbolicArray(SymbolicValue._arg_list_uint(1, input_size), [None], [OptimizedField]))
		body = optimize_expr(symbolize(trace(transform(py_quadraticcircuit_call, 'QuadraticCircuit'), [qc, iv]))[1])
		print(f'QuadraticCircuit.__call__{output_size}_{input_size}', file=trees)
		body._print_tree(file=trees)
		print(file=trees)
		build_function(module, f'QuadraticCircuit.__call__{output_size}_{input_size}', [ArrayType(byte_t, input_size**2 * output_size * OptimizedField.field_power**2).as_pointer(), ArrayType(byte_t, input_size).as_pointer(), ArrayType(byte_t, output_size).as_pointer()], ArrayType(byte_t, output_size).as_pointer(), short_t, long_t, body)
	
	trees.close()
	
	with open('module.ll', 'w') as f:
		print(module, file=f)
	
	print("compiling...")
	engine = create_mcjit_compiler(parse_assembly(str(module)), Target.from_triple(get_process_triple()).create_target_machine())
	engine.finalize_object()
	engine.run_static_constructors()
	print(" ready")
	
	'''
	def field_sum_bridge(l):
		if hasattr(l, 'serialize'):
			l = l.serialize()
			array_t = c_uint8 * len(l)
			l = array_t.from_buffer(l)
		else:
			l = [int(_v) for _v in l]
			array_t = c_uint8 * len(l)
			l = array_t(*l)
		
		c_field_sum = engine.get_function_address(f'Field.sum_{len(l)}')
		if not c_field_sum:
			raise NotImplementedError(f'Field.sum_{len(l)}')
		
		field_sum = CFUNCTYPE(c_uint8, array_t)(c_field_sum)
		return Field(field_sum(l))
	#Field.sum = field_sum_bridge
	'''
	OptimizedField.sum = orig_field_sum
	
	field_mul = CFUNCTYPE(c_uint8, c_uint8, c_uint8)(engine.get_function_address('Field.__mul__'))
	OptimizedField.__mul__ = lambda x, y: OptimizedField(field_mul(c_uint8(int(x)), c_uint8(int(y))))
	
	field_pow = CFUNCTYPE(c_uint8, c_uint8, c_int16)(engine.get_function_address('Field.__pow__'))
	OptimizedField.__pow__ = lambda x, y: OptimizedField(field_pow(c_uint8(int(x)), c_int16(y)))
	
	linear_array_t = c_uint8 * OptimizedField.field_power
	linear_call = CFUNCTYPE(c_uint8, linear_array_t, c_uint8)(engine.get_function_address('Linear.__call__'))
	OptimizedLinear.__call__ = lambda x, y: OptimizedField(linear_call(linear_array_t.from_buffer(x.serialize()), c_uint8(int(y))))
	
	quadratic_array_t = c_uint8 * OptimizedField.field_power**2
	quadratic_call = CFUNCTYPE(c_uint8, quadratic_array_t, c_uint8, c_uint8)(engine.get_function_address('Quadratic.__call__'))
	OptimizedQuadratic.__call__ = lambda x, y, z: OptimizedField(quadratic_call(quadratic_array_t.from_buffer(x.serialize()), c_uint8(int(y)), c_uint8(int(z))))
	
	def linearcircuit_call_bridge(lc, iv):
		assert lc.input_size == len(iv), f"{lc.input_size} == {len(iv)}"
		
		c_linearcircuit_call = engine.get_function_address(f'LinearCircuit.__call__{lc.output_size}_{lc.input_size}')
		if not c_linearcircuit_call:
			raise NotImplementedError(f'LinearCircuit.__call__{lc.output_size}_{lc.input_size}')
		
		assert len(list(lc.serialize())) == lc.output_size * lc.input_size * OptimizedField.field_power, f"{len(list(lc.serialize()))} == {lc.output_size * lc.input_size * OptimizedField.field_power}"
		
		lc_array_t = c_uint8 * (lc.output_size * lc.input_size * OptimizedField.field_power)
		iv_array_t = c_uint8 * lc.input_size
		ov_array_t = c_uint8 * lc.output_size
		
		linearcircuit_call = CFUNCTYPE(ov_array_t, lc_array_t, iv_array_t, ov_array_t)(c_linearcircuit_call)
		
		ov = Vector.zero(lc.output_size, lc.Array, lc.Field)
		linearcircuit_call(lc_array_t.from_buffer(lc.serialize()), iv_array_t.from_buffer(iv.serialize()), ov_array_t.from_buffer(ov.serialize()))
		return ov
	OptimizedLinearCircuit.__call__ = linearcircuit_call_bridge
	
	def quadraticcircuit_call_bridge(qc, iv):
		assert qc.input_size == len(iv)
		
		c_quadraticcircuit_call = engine.get_function_address(f'QuadraticCircuit.__call__{qc.output_size}_{qc.input_size}')
		if not c_quadraticcircuit_call:
			raise NotImplementedError(f'QuadraticCircuit.__call__{qc.output_size}_{qc.input_size}')
		
		assert len(list(qc.serialize())) == qc.output_size * qc.input_size**2 * OptimizedField.field_power**2, f"{len(list(qc.serialize()))} == {qc.output_size * qc.input_size**2 * OptimizedField.field_power**2}"
		
		qc_array_t = c_uint8 * (qc.output_size * qc.input_size**2 * OptimizedField.field_power**2)
		iv_array_t = c_uint8 * qc.input_size
		ov_array_t = c_uint8 * qc.output_size
		
		quadraticcircuit_call = CFUNCTYPE(ov_array_t, qc_array_t, iv_array_t, ov_array_t)(c_quadraticcircuit_call)
		
		ov = Vector.zero(qc.output_size, qc.Array, qc.Field)
		quadraticcircuit_call(qc_array_t.from_buffer(qc.serialize()), iv_array_t.from_buffer(iv.serialize()), ov_array_t.from_buffer(ov.serialize()))
		return ov
	OptimizedQuadraticCircuit.__call__ = quadraticcircuit_call_bridge
	
	# Keep references to compiled code.
	OptimizedField.__module = OptimizedLinear.__module = OptimizedQuadratic.__module = OptimizedLinearCircuit.__module = OptimizedQuadraticCircuit.__module = module
	OptimizedField.__engine = OptimizedLinear.__engine = OptimizedQuadratic.__engine = OptimizedLinearCircuit.__engine = OptimizedQuadraticCircuit.__engine = engine
	
	return OptimizedField, OptimizedLinear, OptimizedQuadratic, OptimizedLinearCircuit, OptimizedQuadraticCircuit


def initialize_llvm():
	initialize()
	initialize_native_target()
	initialize_native_asmprinter()


if __name__ == '__main__':
	from itertools import product
	from random import randrange
	
	from fields import Galois
	from linear import Linear, Quadratic, Vector
	from machines import Automaton, LinearCircuit, QuadraticCircuit
	from memory import Array, Table
	
	from pycallgraph2 import PyCallGraph
	from pycallgraph2.output.graphviz import GraphvizOutput
		
	initialize_llvm()
	
	
	Field = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	
	
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
	
	#SymbolicArray.Field = Field
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
	
	#SymbolicTable.Field = Field
	SymbolicTable.Array = SymbolicArray
	SymbolicTable.Table = SymbolicTable
	
	
	test_vec_1 = [Field.random(randrange) for _n in range(Field.field_power)]
	test_vec_2 = [Field.random(randrange), Field.random(randrange)]
	test_vec_3 = [Field.random(randrange), randrange(Field.field_size)]
	test_vec_4 = [Linear.random(Array, Field, randrange), Field.random(randrange)]
	test_vec_5 = [Quadratic.random(Array, Linear, Field, randrange), Field.random(randrange), Field.random(randrange)]
	
	test_a = (Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]), test_vec_5[0](test_vec_5[1], test_vec_5[2]))
	#print(Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]))
	
	FieldO, LinearO, QuadraticO, LinearCircuitO, QuadraticCircuitO = optimize(Field)
	
	test_b = (Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]), test_vec_5[0](test_vec_5[1], test_vec_5[2]))
	
	print(test_a)
	print(test_b)
	assert test_a == test_b
	#print(Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]))
	
	#input_size = output_size = 8
	#lc = LinearCircuit({(_m, _n):Linear([Field(SymbolicValue._arg_list_uint(0, output_size * input_size * Field.field_power)[Field.field_power * input_size * _m + Field.field_power * _n + _k]) for _k in range(Field.field_power)]) for (_m, _n) in product(range(output_size), range(input_size))}, output_size=output_size, input_size=input_size)
	#v = Vector([Field(_v) for _v in SymbolicValue._arg_list_uint(1, Field.field_power)])
	#build_function(module, 'LinearCircuit.__call__', [..., ...], ..., trace(LinearCircuit.__call__, [lc, v]))
	
	def random_stream(length, size, Array, Field, randbelow):
		for n in range(length):
			yield Vector.random(size, Array, Field, randbelow)
	
	m_impl = 'llvm'
	
	print()
	a_str = list(random_stream(10, 8, Array, Field, randrange))	
	au = Automaton.random_linear_linear(8, 8, 12, Table, Array, Vector, LinearCircuit, Linear, Field, randrange)
	ao = Automaton.deserialize_linear_linear(8, 8, 12, Table, Array, Vector, LinearCircuitO, LinearO, FieldO, au.serialize())
	#with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_linear_linear_{Field.__name__}.png')):
	su = au.init_state[:]
	so = ao.init_state[:]
	print(su, so)
	assert su == so
	for n, (xu, xo) in enumerate(zip(au(a_str, su), ao(a_str, so), strict=True)):
		print(n, xu, xo)
		assert xu == xo
	print(su, so)
	assert su == so
	
	print()
	b_str = list(random_stream(10, 4, Array, Field, randrange))	
	bu = Automaton.random_linear_quadratic(4, 4, 8, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randrange)
	bo = Automaton.deserialize_linear_quadratic(4, 4, 8, Table, Array, Vector, QuadraticCircuitO, LinearCircuitO, QuadraticO, LinearO, FieldO, bu.serialize())
	#with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_linear_quadratic_{Field.__name__}.png')):
	su = bu.init_state[:]
	so = bo.init_state[:]
	print(su, so)
	assert su == so
	for n, (xu, xo) in enumerate(zip(bu(b_str, su), bo(b_str, so), strict=True)):
		print(n, xu, xo)
		assert xu == xo
	print(su, so)
	assert su == so
	
	print()
	c_str = list(random_stream(10, 4, Array, Field, randrange))	
	cu = Automaton.random_quadratic_linear(4, 4, 8, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randrange)
	co = Automaton.deserialize_quadratic_linear(4, 4, 8, Table, Array, Vector, QuadraticCircuitO, LinearCircuitO, QuadraticO, LinearO, FieldO, cu.serialize())
	#with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_quadratic_linear_{Field.__name__}.png')):
	su = cu.init_state[:]
	so = co.init_state[:]
	print(su, so)
	assert su == so
	for n, (xu, xo) in enumerate(zip(cu(c_str, su), co(c_str, so), strict=True)):
		print(n, xu, xo)
		assert xu == xo
	print(su, so)
	assert su == so
	
	print()
	d_str = list(random_stream(10, 1, Array, Field, randrange))
	du = Automaton.random_quadratic_quadratic(1, 1, 16, Table, Array, Vector, QuadraticCircuit, Quadratic, Linear, Field, randrange)
	do = Automaton.deserialize_quadratic_quadratic(1, 1, 16, Table, Array, Vector, QuadraticCircuitO, QuadraticO, LinearO, FieldO, du.serialize())
	#with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_quadratic_quadratic_{Field.__name__}.png')):
	su = du.init_state[:]
	so = do.init_state[:]
	print(su, so)
	assert su == so
	for n, (xu, xo) in enumerate(zip(du(d_str, su), do(d_str, so), strict=True)):
		print(n, xu, xo)
		assert xu == xo
	print(su, so)
	assert su == so


