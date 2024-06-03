#!/usr/bin/python3


from enum import Enum
from ctypes import CFUNCTYPE, c_uint8, c_int16, POINTER
from llvmlite.ir import Module, IntType, ArrayType, Constant, GlobalVariable, FunctionType, Function, IRBuilder
from llvmlite.ir._utils import DuplicatedNameError
from llvmlite.binding import initialize, initialize_native_target, initialize_native_asmprinter, parse_assembly, create_mcjit_compiler, Target, get_process_triple
from collections.abc import Iterable
from itertools import chain


class SymbolicValue:
	Type = Enum('SymbolicValue.Type', 'BOOL INT UINT LIST_INT LIST_UINT')
	Mnemonic = Enum('SymbolicValue.Mnemonic', 'CONST PTR FUN ARG FOR IF LOOP CALL INDEX ADD SUB MUL FLOORDIV MOD NEG POW SHL XOR AND EQ NE GT GE LT LE')
	
	def __init__(self, mnemonic, type_=None, length=None, operands=None):
		

		if type_ is None and length is None and operands is None:
			if not isinstance(mnemonic, self.__class__) and not isinstance(mnemonic, int) and not isinstance(mnemonic, Iterable):
				try:
					newargs = mnemonic.__getnewargs__()[0]
				except AttributeError:
					pass
				else:
					if isinstance(newargs, self.__class__):
						mnemonic = newargs
			
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
				elif isinstance(mnemonic, Iterable):
					self.__mnemonic = self.Mnemonic.CONST
					values = [self.__class__(v) for v in mnemonic]
					t = frozenset(_v.__type for _v in values)
					if t == frozenset({self.Type.INT, self.Type.UINT}):
						self.__type = self.Type.LIST_INT
					elif t == frozenset({self.Type.UINT}):
						self.__type = self.Type.LIST_UINT
					else:
						raise ValueError(f"List must be flat collection of ints. Got: {values}")
					self.__length = len(values)
					self.__operands = values
				else:
					raise ValueError(f"Could not convert value to SymbolicValue: {type(mnemonic)}.")
		else:
			self.__mnemonic = mnemonic
			self.__type = type_
			self.__length = length
			self.__operands = operands
	
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
	def _fun_int(cls, v):
		return cls(cls.Mnemonic.FUN, cls.Type.INT, None, v)
	
	@classmethod
	def _fun_uint(cls, v):
		return cls(cls.Mnemonic.FUN, cls.Type.UINT, None, v)
	
	@classmethod
	def _fun_list_int(cls, v, l):
		return cls(cls.Mnemonic.FUN, cls.Type.LIST_INT, l, v)
	
	@classmethod
	def _fun_list_uint(cls, v, l):
		return cls(cls.Mnemonic.FUN, cls.Type.LIST_UINT, l, v)
	
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
	def _for(cls, n, l):
		return cls(cls.Mnemonic.FOR, cls.Type.UINT, None, [n, l])
	
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
		try:
			index = self.__class__(index)
		except ValueError:
			return NotImplemented
		
		if index.__type not in (self.Type.INT, self.Type.UINT):
			raise TypeError(f"Can not use {index} as index.")
		
		if self.__type == self.Type.LIST_INT:
			type_ = self.Type.INT
		elif self.__type == self.Type.LIST_UINT:
			type_ = self.Type.UINT
		else:
			raise TypeError(f"Can not take item of {self}.")
		
		return self.__class__(self.Mnemonic.INDEX, type_, None, [self, index])
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + self.__mnemonic.name + ', ' + self.__type.name + ', ' + repr(self.__length) + ', ' + repr(self.__operands) + ')'
	
	def __bool__(self):
		state = self._state()
		if state in boolean_values:
			return boolean_values[state]
		else:
			raise BooleanQuery(self)
	
	def _state(self):
		return (self.__mnemonic, self.__type, self.__length, tuple(_op._state() if hasattr(_op, '_state') else _op for _op in self.__operands) if isinstance(self.__operands, list) else self.__operands)


boolean_values = {}


class BooleanQuery(BaseException):
	def __init__(self, value):
		self.value = value


def trace(fn, args):
	boolean_values.clear()
	
	def path():
		try:
			return SymbolicValue(fn(*args))
		except BooleanQuery as bq:
			state = bq.value._state()
			
			boolean_values[state] = True
			yes = path()
			
			boolean_values[state] = False
			no = path()
			
			del boolean_values[state]
			
			if yes is None:
				return no
			elif no is None:
				return yes
			else:
				return SymbolicValue._if(bq.value, yes, no)
		except ArithmeticError:
			return None
	
	return path()


def build_array(module, name, int_t, array):
	array_t = ArrayType(int_t, len(array._SymbolicValue__operands))
	result = GlobalVariable(module, array_t, name)
	result.initializer = array_t([int_t(_n._SymbolicValue__operands) for _n in array._SymbolicValue__operands])
	result.global_constant = True


def build_function(module, name, args_t, return_t, expr):
	int_t = IntType(16)
	bool_t = IntType(1)
	
	function_t = FunctionType(return_t, args_t)
	try:
		function = Function(module, function_t, name)
	except DuplicatedNameError:
		function = module.get_global(name)
	assert function.type.pointee == function_t, f"{function.type} == {function_t}"
	
	if expr is None:
		assert function.is_declaration
		return
	
	def assemble(expr, builder):
		if isinstance(expr._SymbolicValue__operands, Iterable) and not isinstance(expr._SymbolicValue__operands, str):
			if expr._SymbolicValue__mnemonic == expr.Mnemonic.IF:
				c, yes, no = expr._SymbolicValue__operands
				
				if isinstance(c, SymbolicValue) and c._SymbolicValue__mnemonic != expr.Mnemonic.CONST:
					c, c_builder = assemble(c, builder)
					if c.type != bool_t:
						c = c_builder.icmp_signed('!=', c, int_t(0))
					
					yes_builder_enter = IRBuilder(function.append_basic_block())
					yes_r, yes_builder_exit = assemble(yes, yes_builder_enter)
					no_builder_enter = IRBuilder(function.append_basic_block())
					no_r, no_builder_exit = assemble(no, no_builder_enter)
					
					assert yes_r.type == no_r.type
					
					c_builder.cbranch(c, yes_builder_enter.block, no_builder_enter.block)
					r_builder = IRBuilder(function.append_basic_block())
					yes_builder_exit.branch(r_builder.block)
					no_builder_exit.branch(r_builder.block)
					
					phi = r_builder.phi(yes_r.type)
					phi.add_incoming(yes_r, yes_builder_exit.block)
					phi.add_incoming(no_r, no_builder_exit.block)
					return phi, r_builder
				else:
					raise NotImplementedError
			
			else:
				args = []
				for e in expr._SymbolicValue__operands:
					if isinstance(e, SymbolicValue):
						r, builder = assemble(e, builder)
					else:
						r = e
					args.append(r)
			
			if expr._SymbolicValue__mnemonic == expr.Mnemonic.CONST:
				if expr._SymbolicValue__type == expr.Type.LIST_INT or expr._SymbolicValue__type == expr.Type.LIST_UINT:
					#print("return list", len(expr._SymbolicValue__), args)
					assert len(expr._SymbolicValue__operands) == len(args)
					return args, builder
				else:
					raise NotImplementedError(str(expr._SymbolicValue__type))
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.INDEX:
				#print(args[0].type)
				p = builder.gep(args[0], [int_t(0), args[1]])
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
				return builder.xor(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.ADD:
				return builder.add(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.MUL:
				return builder.mul(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.GE:
				return builder.icmp_signed('>=', args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.MOD:
				if expr._SymbolicValue__operands[1]._SymbolicValue__type != expr.Type.UINT:
					raise NotImplementedError(str(expr._SymbolicValue__operands[1]._SymbolicValue__type))
				
				if expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.INT:
					return builder.urem(args[0], args[1]), builder # urem in Python semantics
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.UINT:
					return builder.urem(args[0], args[1]), builder
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
				
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.CALL:
				fn = args[0]
				
				tr_args = []
				#print(fn.type.pointee, dir(fn.type.pointee))
				for a, tt in zip(args[1:], fn.type.pointee.args):
					if isinstance(a, list):
						l = builder.alloca(tt.pointee)
						for n, el in enumerate(a):
							#print(tt.pointee, dir(tt.pointee))
							p = builder.gep(l, [int_t(0), int_t(n)])
							v = builder.trunc(el, tt.pointee.element)
							builder.store(v, p)
						a = l
					elif a.type != tt:
						a = builder.trunc(a, tt)
					tr_args.append(a)
				
				r = builder.call(fn, tr_args)
				if expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.INT:
					#builder.comment("signed function result")
					r = builder.sext(r, int_t)
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.UINT:
					r = builder.zext(r, int_t)
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
				
				return r, builder
			
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
			else:
				raise NotImplementedError(str(expr))
	
	builder = IRBuilder(function.append_basic_block())
	result, builder = assemble(expr, builder)
	if isinstance(result, list):
		assert return_t == args_t[-1]
		assert len(result) == return_t.pointee.count, f"{function_t} ;;; {function.type}"
		#print("return list", name, len(result), return_t)
		r = function.args[len(args_t) - 1]
		for n, val in enumerate(result):
			p = builder.gep(r, [int_t(0), int_t(n)])
			#print(return_t, dir(return_t.pointee), return_t.pointee.element)
			v = builder.trunc(val, return_t.pointee.element)
			builder.store(v, p)
	else:
		r = builder.trunc(result, return_t)
	builder.ret(r)



byte_t = IntType(8)
short_t = IntType(16)


def optimize(Field):
	module = Module()
	
	build_array(module, 'Field.exponent', byte_t, SymbolicValue(Field.exponent))
	build_array(module, 'Field.logarithm', byte_t, SymbolicValue(Field.logarithm))
	
	Field.exponent = SymbolicValue._ptr_list_uint('Field.exponent', 256)
	Field.logarithm = SymbolicValue._ptr_list_uint('Field.logarithm', 256)
	
	field_sum_types = set()
	py_field_sum = Field.sum
	def field_sum_capture(l):
		l = [SymbolicValue(_f) for _f in l]
		if len(l) not in field_sum_types:
			field_sum_types.add(len(l))
			build_function(module, f'Field.sum_{len(l)}', [ArrayType(byte_t, len(l)).as_pointer()], byte_t, None)
		return SymbolicValue._fun_uint(f'Field.sum_{len(l)}')(l)
	Field.sum = field_sum_capture
	
	build_function(module, 'Field.__mul__', [byte_t, byte_t], byte_t, trace(Field.__mul__, [Field(SymbolicValue._arg_uint(0)), Field(SymbolicValue._arg_uint(1))]))
	Field.__mul__ = lambda _a, _b: Field(SymbolicValue._fun_uint('Field.__mul__')(SymbolicValue(_a), SymbolicValue(_b)))
	
	build_function(module, 'Field.__pow__', [byte_t, short_t], byte_t, trace(Field.__pow__, [Field(SymbolicValue._arg_uint(0)), SymbolicValue._arg_int(1)]))
	Field.__pow__ = lambda _a, _b: Field(SymbolicValue._fun_uint('Field.__pow__')(SymbolicValue(_a), SymbolicValue(_b)))
	
	build_function(module, 'Linear.__call__', [ArrayType(byte_t, Field.field_power).as_pointer(), byte_t], byte_t, trace(Linear.__call__, [Linear([Field(SymbolicValue._arg_list_uint(0, Field.field_power)[_n]) for _n in range(Field.field_power)]), Field(SymbolicValue._arg_uint(1))]))
	Linear.__call_ = lambda _l, _f: Field(SymbolicValue._fun_uint('Linear.__call__')(SymbolicValue(_l), SymbolicValue(_f)))
	
	build_function(module, 'Quadratic.__call__', [ArrayType(byte_t, Field.field_power**2).as_pointer(), byte_t, byte_t], byte_t, trace(Quadratic.__call__, [Quadratic([Linear([Field(SymbolicValue._arg_list_uint(0, Field.field_power**2)[Field.field_power * m + n]) for n in range(Field.field_power)]) for m in range(Field.field_power)]), Field(SymbolicValue._arg_uint(1)), Field(SymbolicValue._arg_uint(2))]))
	Quadratic.__call_ = lambda _q, _f1, _f2: Field(SymbolicValue._fun_uint('Quadratic.__call__')(SymbolicValue(_q), SymbolicValue(_f1), SymbolicValue(_f2)))
	
	linearcircuit_call_types = set()
	py_linearcircuit_call = LinearCircuit.__call__
	def linearcircuit_call_capture(lc, iv):
		lc = list(chain.from_iterable((SymbolicValue(lc[_o, _i].linear_coefficient(_k) for _k in range(Field.field_power))) for _o, _i in product(range(lc.output_size), range(lc.input_size))))
		iv = [SymbolicValue(_f) for _f in iv]
		
		len_lc = len(lc) // Field.field_power
		len_iv = len(iv)
		assert len_lc % len_iv == 0, f"{len_lc}, {len_iv}"
		len_ov = len_lc // len_iv
		
		if (len_ov, len_iv) not in linearcircuit_call_types:
			linearcircuit_call_types.add((len_ov, len_iv))
			build_function(module, f'LinearCircuit.__call__{len_ov}_{len_iv}', [ArrayType(byte_t, len_lc * Field.field_power).as_pointer(), ArrayType(byte_t, len_iv).as_pointer(), ArrayType(byte_t, len_ov).as_pointer()], ArrayType(byte_t, len_ov).as_pointer(), None)
		return SymbolicValue._fun_uint(f'LinearCircuit.__call__{len_ov}_{len_iv}')(lc, iv)
	LinearCircuit.__call__ = linearcircuit_call_capture
	
	'''
	quadraticcircuit_call_types = set()
	py_quadraticcircuit_call = QuadraticCircuit.__call__
	def quadraticcircuit_call_capture(qc, iv):
		print(qc.output_size, qc.input_size, qc[qc.output_size - 1, qc.input_size - 1, qc.input_size - 1])
		qc = list(chain.from_iterable((SymbolicValue(qc[_o, _i, _j].quadratic_coefficient(_k, _l) for _k, _l in product(range(Field.field_power), range(Field.field_power)))) for _o, _i, _j in product(range(qc.output_size), range(qc.input_size), range(qc.input_size))))
		iv = [SymbolicValue(_f) for _f in iv]
		
		len_qc = len(qc) // Field.field_power**2
		len_iv = len(iv)
		assert len_qc % len_iv**2 == 0, f"{len_qc}, {len_iv}"
		len_ov = len_qc // len_iv**2
		
		if (len_ov, len_iv) not in quadraticcircuit_call_types:
			quadraticcircuit_call_types.add((len_ov, len_iv))
			build_function(module, f'QuadraticCircuit.__call__{len_ov}_{len_iv}', [ArrayType(byte_t, len_qc * Field.field_power**2).as_pointer(), ArrayType(byte_t, len_iv).as_pointer(), ArrayType(byte_t, len_ov).as_pointer()], ArrayType(byte_t, len_ov).as_pointer(), None)
		return SymbolicValue._fun_uint(f'QuadraticCircuit.__call__{len_ov}_{len_iv}')(qc, iv)
	QuadraticCircuit.__call__ = quadraticcircuit_call_capture
	'''
	
	for output_size, input_size in [(4, 12), (8, 12), (8, 20), (12, 20)]:
		lc = LinearCircuit({(_i, _j):Linear([Field(SymbolicValue._arg_list_uint(0, Field.field_power * output_size * input_size)[_i * input_size * Field.field_power + _j * Field.field_power + _k]) for _k in range(Field.field_power)]) for (_i, _j) in product(range(output_size), range(input_size))})
		iv = Vector([Field(SymbolicValue._arg_list_uint(1, input_size)[_i]) for _i in range(input_size)])
		tr = lc(iv)
	
	arg = SymbolicValue._arg_list_uint(0, Field.field_power**2 * output_size * input_size**2)
	n = 0
	qs = {}
	for output_size, input_size in [(4, 12)]:
		for o, i, j in product(range(output_size), range(input_size), range(input_size)):
			ls = []
			for k in range(Field.field_power):
				fs = []
				for l in range(Field.field_power):
					fs.append(Field(arg[n]))
					n += 1
				ls.append(Linear(fs))
			qs[o, i, j] = Quadratic(ls)
		qc = QuadraticCircuit(qs)
		
		iv = Vector([Field(SymbolicValue._arg_list_uint(1, input_size)[_i]) for _i in range(input_size)])
		tr = qc(iv)
	
	#field_sum_types.add(144)
	field_sum_types.add(289)
	
	print(field_sum_types, linearcircuit_call_types) #, quadraticcircuit_call_types)
	
	for output_size, input_size in linearcircuit_call_types:
		lc = LinearCircuit({(_i, _j):Linear([Field(SymbolicValue._arg_list_uint(0, Field.field_power * output_size * input_size)[_i * input_size * Field.field_power + _j * Field.field_power + _k]) for _k in range(Field.field_power)]) for (_i, _j) in product(range(output_size), range(input_size))})
		iv = Vector([Field(SymbolicValue._arg_list_uint(1, input_size)[_i]) for _i in range(input_size)])
		tr = trace((lambda _lc, _iv: py_linearcircuit_call(_lc, _iv).serialize()), [lc, iv])
		print("implement", f'LinearCircuit.__call__{output_size}_{input_size}')
		build_function(module, f'LinearCircuit.__call__{output_size}_{input_size}', [ArrayType(byte_t, input_size * output_size * Field.field_power).as_pointer(), ArrayType(byte_t, input_size).as_pointer(), ArrayType(byte_t, output_size).as_pointer()], ArrayType(byte_t, output_size).as_pointer(), tr)
	
	'''
	for output_size, input_size in quadraticcircuit_call_types:
		qc = QuadraticCircuit({(_o, _i, _j):Quadratic([Linear([Field(SymbolicValue._arg_list_uint(0, Field.field_power**2 * output_size * input_size**2)[_i * input_size * Field.field_power**2 + _j * Field.field_power**2 + _k * Field.field_power + _l]) for _k in range(Field.field_power)]) for _l in range(Field.field_power)]) for (_o, _i, _j) in product(range(output_size), range(input_size), range(input_size))})
		iv = Vector([Field(SymbolicValue._arg_list_uint(1, input_size)[_i]) for _i in range(input_size)])
		tr = trace((lambda _qc, _iv: py_quadraticcircuit_call(_qc, _iv).serialize()), [qc, iv])
		print("implement", f'QuadraticCircuit.__call__{output_size}_{input_size}')
		build_function(module, f'QuadraticCircuit.__call__{output_size}_{input_size}', [ArrayType(byte_t, input_size**2 * output_size * Field.field_power**2).as_pointer(), ArrayType(byte_t, input_size).as_pointer(), ArrayType(byte_t, output_size).as_pointer()], ArrayType(byte_t, output_size).as_pointer(), tr)
	'''
	
	for l in field_sum_types:
		print("implement", f'Field.sum_{l}')
		build_function(module, f'Field.sum_{l}', [ArrayType(byte_t, l).as_pointer()], byte_t, trace(py_field_sum, [[Field(SymbolicValue._arg_list_uint(0, l)[_n]) for _n in range(l)]]))
	
	print("compiling...")
	engine = create_mcjit_compiler(parse_assembly(str(module)), Target.from_triple(get_process_triple()).create_target_machine())
	engine.finalize_object()
	engine.run_static_constructors()
	print(" ready")
	
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
	Field.sum = field_sum_bridge
	
	field_mul = CFUNCTYPE(c_uint8, c_uint8, c_uint8)(engine.get_function_address('Field.__mul__'))
	Field.__mul__ = lambda x, y: Field(field_mul(c_uint8(int(x)), c_uint8(int(y))))
	
	field_pow = CFUNCTYPE(c_uint8, c_uint8, c_int16)(engine.get_function_address('Field.__pow__'))
	Field.__pow__ = lambda x, y: Field(field_pow(c_uint8(int(x)), c_int16(y)))
	
	linear_array_t = c_uint8 * Field.field_power
	linear_call = CFUNCTYPE(c_uint8, linear_array_t, c_uint8)(engine.get_function_address('Linear.__call__'))
	Linear.__call__ = lambda x, y: Field(linear_call(linear_array_t.from_buffer(x.serialize()), c_uint8(int(y))))
	
	quadratic_array_t = c_uint8 * Field.field_power**2
	quadratic_call = CFUNCTYPE(c_uint8, quadratic_array_t, c_uint8, c_uint8)(engine.get_function_address('Quadratic.__call__'))
	Quadratic.__call__ = lambda x, y, z: Field(quadratic_call(quadratic_array_t.from_buffer(x.serialize()), c_uint8(int(y)), c_uint8(int(z))))
	
	def linearcircuit_call_bridge(lc, iv):
		assert lc.input_size == len(iv)
		
		c_linearcircuit_call = engine.get_function_address(f'LinearCircuit.__call__{lc.output_size}_{lc.input_size}')
		if not c_linearcircuit_call:
			raise NotImplementedError(f'LinearCircuit.__call__{lc.output_size}_{lc.input_size}')
		
		lc_array_t = c_uint8 * (lc.output_size * lc.input_size * Field.field_power)
		iv_array_t = c_uint8 * lc.input_size
		ov_array_t = c_uint8 * lc.output_size
		
		linearcircuit_call = CFUNCTYPE(ov_array_t, lc_array_t, iv_array_t, ov_array_t)(c_linearcircuit_call)
		
		ov = Vector.zero(lc.output_size, lc.Array, lc.Field)
		linearcircuit_call(lc_array_t.from_buffer(lc.serialize()), iv_array_t.from_buffer(iv.serialize()), ov_array_t.from_buffer(ov.serialize()))
		return ov
	LinearCircuit.__call__ = linearcircuit_call_bridge
	
	'''
	def quadraticcircuit_call_bridge(qc, iv):
		assert qc.input_size == len(iv)
		
		c_quadraticcircuit_call = engine.get_function_address(f'QuadraticCircuit.__call__{qc.output_size}_{qc.input_size}')
		if not c_quadraticcircuit_call:
			raise NotImplementedError(f'QuadraticCircuit.__call__{qc.output_size}_{qc.input_size}')
		
		qc_array_t = c_uint8 * (qc.output_size * qc.input_size**2 * Field.field_power**2)
		iv_array_t = c_uint8 * qc.input_size
		ov_array_t = c_uint8 * qc.output_size
		
		quadraticcircuit_call = CFUNCTYPE(ov_array_t, qc_array_t, iv_array_t, ov_array_t)(c_quadraticcircuit_call)
		
		ov = Vector.zero(qc.output_size, qc.Array, qc.Field)
		quadraticcircuit_call(qc_array_t.from_buffer(qc.serialize()), iv_array_t.from_buffer(iv.serialize()), ov_array_t.from_buffer(ov.serialize()))
		return ov
	QuadraticCircuit.__call__ = quadraticcircuit_call_bridge
	'''
	
	# Keep references to compiled code.
	Field.__module = Linear.__module = Quadratic.__module = LinearCircuit.__module = QuadraticCircuit.__module = module
	Field.__engine = Linear.__engine = Quadratic.__engine = LinearCircuit.__engine = QuadraticCircuit.__engine = engine
	
	#print(module)
	
	return Field, Linear, Quadratic, LinearCircuit, QuadraticCircuit


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
	#Array = list
	#Table = dict

	from pycallgraph2 import PyCallGraph
	from pycallgraph2.output.graphviz import GraphvizOutput
	
	initialize_llvm()
	
	Field = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	
	test_vec_1 = [Field.random(randrange) for _n in range(Field.field_power)]
	test_vec_2 = [Field.random(randrange), Field.random(randrange)]
	test_vec_3 = [Field.random(randrange), randrange(Field.field_size)]
	test_vec_4 = [Linear.random(Array, Field, randrange), Field.random(randrange)]
	test_vec_5 = [Quadratic.random(Array, Linear, Field, randrange), Field.random(randrange), Field.random(randrange)]
	
	print(Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]), test_vec_5[0](test_vec_5[1], test_vec_5[2]))
	
	Field, Linear, Quadratic, LinearCircuit, QuadraticCircuit = optimize(Field)
	
	print(Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]), test_vec_5[0](test_vec_5[1], test_vec_5[2]))
	
	#input_size = output_size = 8
	#lc = LinearCircuit({(_m, _n):Linear([Field(SymbolicValue._arg_list_uint(0, output_size * input_size * Field.field_power)[Field.field_power * input_size * _m + Field.field_power * _n + _k]) for _k in range(Field.field_power)]) for (_m, _n) in product(range(output_size), range(input_size))}, output_size=output_size, input_size=input_size)
	#v = Vector([Field(_v) for _v in SymbolicValue._arg_list_uint(1, Field.field_power)])
	#build_function(module, 'LinearCircuit.__call__', [..., ...], ..., trace(LinearCircuit.__call__, [lc, v]))


	def random_stream(length, size, Array, Field, randbelow):
		for n in range(length):
			yield Vector.random(size, Array, Field, randbelow)
	
	m_impl = 'llvm'
	
	a = Automaton.random_linear_linear(8, 8, 12, Table, Array, Vector, LinearCircuit, Linear, Field, randrange)
	with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_linear_linear_{Field.__name__}.png')):
		print()
		s = a.init_state[:]
		print(s)
		for n, x in enumerate(a(random_stream(1000, 8, Array, Field, randrange), s)):
			print(n, x)
		print(s)
	
	b = Automaton.random_linear_quadratic(4, 4, 8, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randrange)
	with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_linear_quadratic_{Field.__name__}.png')):
		print()
		s = b.init_state[:]
		print(s)
		for n, x in enumerate(b(random_stream(10, 4, Array, Field, randrange), s)):
			print(n, x)
		print(s)
	
	c = Automaton.random_quadratic_linear(4, 4, 8, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randrange)
	with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_quadratic_linear_{Field.__name__}.png')):
		print()
		s = c.init_state[:]
		print(s)
		for n, x in enumerate(c(random_stream(10, 4, Array, Field, randrange), s)):
			print(n, x)
		print(s)
	
	d = Automaton.random_quadratic_quadratic(1, 1, 16, Table, Array, Vector, QuadraticCircuit, Quadratic, Linear, Field, randrange)
	with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_quadratic_quadratic_{Field.__name__}.png')):
		print()
		s = d.init_state[:]
		print(s)
		for n, x in enumerate(d(random_stream(10, 1, Array, Field, randrange), s)):
			print(n, x)
		print(s)






