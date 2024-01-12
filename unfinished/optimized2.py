#!/usr/bin/python3


from enum import Enum
from memory import *
from utils import sm_range
import llvmlite.ir
from fields import Galois, BinaryGalois
from linear import *
from math import ceil
from pathlib import Path
from collections.abc import Generator
from inspect import getfullargspec, stack
from ctypes import py_object, c_int, pythonapi


class ConditionError(Exception):
	pass


class SymbolicValue:
	Mnemonic = Enum('SymbolicValue.Mnemonic', 'LITERAL ARG FOR CALL0 CALL1 CALL2 INDEX RANGE ADD SUB MUL FLOORDIV MOD NEG POW SHL XOR EQ NE GT GE LT LE')
	
	def __init__(self, mnemonic, *operands, length=None):
		try:
			self.__mnemonic = mnemonic.__mnemonic
			self.__operands = mnemonic.__operands
			#if hasattr(mnemonic, '_SymbolicValue__length'):
			#	self.__length = mnemonic.__length
		except AttributeError:
			if isinstance(mnemonic, self.Mnemonic):
				self.__mnemonic = mnemonic
				self.__operands = operands
			else:
				if operands:
					raise TypeError
				self.__init__(self.Mnemonic.LITERAL, mnemonic)
		
		#if length is not None:
		#	self.__length = length
	
	@classmethod
	def make_arg(cls, n):
		if not isinstance(n, int):
			raise ValueError
		return cls(cls.Mnemonic.ARG, n)
	
	@classmethod
	def make_for(cls, n):
		if not isinstance(n, int):
			raise ValueError
		return cls(cls.Mnemonic.FOR, n)
	
	def __int__(self):
		v = self.evaluate()
		if not isinstance(v, int):
			raise ValueError(f"Not int: {v}, {type(v)}")
		return v
	
	def __traverse(self, action):
		#if isinstance(self, int):
		#	return action(self)
		if self.__mnemonic in [self.Mnemonic.LITERAL, self.Mnemonic.ARG, self.Mnemonic.FOR]:
			return action(self)
		
		elif len(self.__operands) == 0:
			return action(self)
		
		elif len(self.__operands) == 1:
			if not hasattr(self.__operands[0], '_SymbolicValue__traverse'):
				x = action(self.__operands[0])
			else:
				x = self.__operands[0].__traverse(action)
			
			return action(self, x=x)
		
		elif len(self.__operands) == 2:
			if not hasattr(self.__operands[0], '_SymbolicValue__traverse'):
				x = action(self.__operands[0])
			else:
				x = self.__operands[0].__traverse(action)
			
			if not hasattr(self.__operands[1], '_SymbolicValue__traverse'):
				y = action(self.__operands[1])
			else:
				y = self.__operands[1].__traverse(action)
			
			return action(self, x=x, y=y)
		
		elif len(self.__operands) == 3:
			if not hasattr(self.__operands[0], '_SymbolicValue__traverse'):
				x = action(self.__operands[0])
			else:
				x = self.__operands[0].__traverse(action)
			
			if not hasattr(self.__operands[1], '_SymbolicValue__traverse'):
				y = action(self.__operands[1])
			else:
				y = self.__operands[1].__traverse(action)
			
			if not hasattr(self.__operands[2], '_SymbolicValue__traverse'):
				z = action(self.__operands[2])
			else:
				z = self.__operands[2].__traverse(action)
			
			return action(self, x=x, y=y, z=z)
		
		else:
			raise NotImplementedError
	
	def evaluate(self):
		def action(node, x=None, y=None, z=None):
			if isinstance(node, int):
				return node
			elif node.__mnemonic == self.Mnemonic.LITERAL:
				return node.__operands[0]
			elif node.__mnemonic == self.Mnemonic.ARG or node.__mnemonic == self.Mnemonic.FOR:
				return NotImplemented
			elif node.__mnemonic == self.Mnemonic.CALL0:
				return x()
			elif node.__mnemonic == self.Mnemonic.CALL1:
				return x(y)
			elif node.__mnemonic == self.Mnemonic.CALL2:
				return x(y, z)
			elif node.__mnemonic == self.Mnemonic.INDEX:
				return x[y]
			elif node.__mnemonic == self.Mnemonic.NEG:
				return -x
			elif node.__mnemonic == self.Mnemonic.ADD:
				return x + y
			elif node.__mnemonic == self.Mnemonic.SUB:
				return x - y
			elif node.__mnemonic == self.Mnemonic.MUL:
				return x * y
			elif node.__mnemonic == self.Mnemonic.FLOORDIV:
				return x // y
			elif node.__mnemonic == self.Mnemonic.POW:
				return x ** y
			elif node.__mnemonic == self.Mnemonic.SHL:
				return x << y
			elif node.__mnemonic == self.Mnemonic.XOR:
				return x ^ y
			elif node.__mnemonic == self.Mnemonic.MOD:
				return x % y
			elif node.__mnemonic == self.Mnemonic.GT:
				if type(x) != type(y):
					return NotImplemented
				else:
					return x > y
			elif node.__mnemonic == self.Mnemonic.GE:
				if type(x) != type(y):
					return NotImplemented
				else:
					return x >= y
			elif node.__mnemonic == self.Mnemonic.LT:
				if type(x) != type(y):
					return NotImplemented
				else:
					return x < y
			elif node.__mnemonic == self.Mnemonic.LE:
				if type(x) != type(y):
					return NotImplemented
				else:
					return x <= y
			elif node.__mnemonic == self.Mnemonic.EQ:
				if type(x) != type(y):
					return NotImplemented
				else:
					return x == y
			elif node.__mnemonic == self.Mnemonic.NE:
				if type(x) != type(y):
					return NotImplemented
				else:
					return x != y
			elif node.__mnemonic == self.Mnemonic.RANGE:
				return range(x)
			else:
				raise NotImplementedError(f"Could not evaluate: {node.__mnemonic.name}")
		
		return self.__traverse(action)
	
	def compile_(self, builder, args, fors, symbols, int_t):
		def action(node, x=None, y=None, z=None):
			if isinstance(node, int) or node is None:
				return node
			elif node.__mnemonic == self.Mnemonic.LITERAL:
				v = node.__operands[0]
				
				if isinstance(v, int):
					v = int_t(v)
				elif isinstance(v, str):
					v = symbols[v]
				else:
					raise NotImplementedError
				
				return v
			elif node.__mnemonic == self.Mnemonic.ARG:
				return args[node.__operands[0]]
			elif node.__mnemonic == self.Mnemonic.FOR:
				return fors[node.__operands[0]]
			elif node.__mnemonic == self.Mnemonic.CALL0:
				return builder.call(x, [])
			elif node.__mnemonic == self.Mnemonic.CALL1:
				y = builder.trunc(y, x.args[0].type)
				return builder.call(x, [y])
			elif node.__mnemonic == self.Mnemonic.CALL2:
				y = builder.trunc(y, x.args[0].type)
				z = builder.trunc(z, x.args[1].type)
				return builder.call(x, [y, z])
			elif node.__mnemonic == self.Mnemonic.INDEX:
				return builder.load(builder.gep(x, [int_t(0), y]))
			elif node.__mnemonic == self.Mnemonic.NEG:
				return builder.neg(x)
			elif node.__mnemonic == self.Mnemonic.ADD:
				return builder.add(builder.zext(x, int_t), builder.zext(y, int_t))
			elif node.__mnemonic == self.Mnemonic.SUB:
				return builder.sub(builder.zext(x, int_t), builder.zext(y, int_t))
			elif node.__mnemonic == self.Mnemonic.MUL:
				return builder.mul(builder.zext(x, int_t), builder.zext(y, int_t))
			elif node.__mnemonic == self.Mnemonic.FLOORDIV:
				return builder.udiv(builder.zext(x, int_t), builder.zext(y, int_t))
			elif node.__mnemonic == self.Mnemonic.POW:
				return builder.call(symbols['pow'], [builder.zext(x, int_t), builder.zext(y, int_t)])
			elif node.__mnemonic == self.Mnemonic.SHL:
				return builder.shl(builder.zext(x, int_t), builder.zext(y, int_t))
			elif node.__mnemonic == self.Mnemonic.XOR:
				return builder.xor(x, y)
			elif node.__mnemonic == self.Mnemonic.MOD:
				return builder.urem(builder.zext(x, y.type), y)
			elif node.__mnemonic == self.Mnemonic.GT:
				return builder.icmp_signed('>', x, y)
			elif node.__mnemonic == self.Mnemonic.GE:
				return builder.icmp_signed('>=', x, y)
			elif node.__mnemonic == self.Mnemonic.LT:
				return builder.icmp_signed('<=', x, y)
			elif node.__mnemonic == self.Mnemonic.LE:
				return builder.icmp_signed('<', x, y)
			elif node.__mnemonic == self.Mnemonic.EQ:
				return builder.icmp_signed('==', x, y)
			elif node.__mnemonic == self.Mnemonic.NE:
				return builder.icmp_signed('!=', x, y)
			else:
				raise NotImplementedError(f"Could not compile: {node.__mnemonic.name}")
		
		return self.__traverse(action)
	
	def extract_args(self):
		def action(node, x=None, y=None, z=None):
			if isinstance(node, int):
				return frozenset()
			elif node.__mnemonic == self.Mnemonic.FOR:
				return frozenset([node])
			else:
				return frozenset().union(x if x is not None else [], y if y is not None else [], z if z is not None else [])
		
		return self.__traverse(action)
	
	def extract_fors(self):
		def action(node, x=None, y=None, z=None):
			if isinstance(node, int):
				return frozenset()
			elif node.__mnemonic == self.Mnemonic.FOR:
				return frozenset([node])
			else:
				return frozenset().union(x if x is not None else [], y if y is not None else [], z if z is not None else [])
		
		return self.__traverse(action)
	
	def __str__(self):
		def action(node, x=None, y=None, z=None):
			if isinstance(node, int) or isinstance(node, str):
				return str(node)
			elif node.__mnemonic == self.Mnemonic.LITERAL:
				return str(node.__operands[0])
			elif node.__mnemonic == self.Mnemonic.ARG:
				return "$" + str(node.__operands[0])
			elif node.__mnemonic == self.Mnemonic.FOR:
				return "£" + str(node.__operands[0])
			elif node.__mnemonic == self.Mnemonic.NEG:
				return f"NEG({x})"
			elif node.__mnemonic == self.Mnemonic.CALL0:
				return f"FUN({x})()"
			elif node.__mnemonic == self.Mnemonic.CALL1:
				return f"FUN({x})({y})"
			elif node.__mnemonic == self.Mnemonic.CALL2:
				return f"FUN({x})({y}, {z})"
			elif node.__mnemonic == self.Mnemonic.INDEX:
				return f"ARRAY({x})[{y}]"
			elif node.__mnemonic == self.Mnemonic.RANGE:
				return f"RANGE({x})"
			else:
				return f"{node.__mnemonic.name}({x}, {y})"
		
		return self.__traverse(action)
	
	def __repr__(self):
		return f'{self.__class__.__name__}({self.__mnemonic.name}, {", ".join([repr(_op) for _op in self.__operands])})'
	
	def __format__(self, f):
		return str(self)
	
	def __add__(self, other):
		return self.__class__(self.Mnemonic.ADD, self, self.__class__(other))
	
	def __radd__(self, other):
		return self.__class__(self.Mnemonic.ADD, self.__class__(other), self)
	
	def __sub__(self, other):
		return self.__class__(self.Mnemonic.SUB, self, self.__class__(other))
	
	def __rsub__(self, other):
		return self.__class__(self.Mnemonic.SUB, self.__class__(other), self)
	
	def __mul__(self, other):
		return self.__class__(self.Mnemonic.MUL, self, self.__class__(other))
	
	def __rmul__(self, other):
		return self.__class__(self.Mnemonic.MUL, self.__class__(other), self)
	
	def __floordiv__(self, other):
		return self.__class__(self.Mnemonic.FLOORDIV, self, self.__class__(other))
	
	def __neg__(self):
		return self.__class__(self.Mnemonic.NEG, self)
	
	def __rlshift__(self, other):
		return self.__class__(self.Mnemonic.SHL, self.__class__(other), self)
	
	def __pow__(self, other):
		return self.__class__(self.Mnemonic.POW, self, self.__class__(other))
	
	def __rpow__(self, other):
		return self.__class__(self.Mnemonic.POW, self.__class__(other), self)
	
	def __xor__(self, other):
		return self.__class__(self.Mnemonic.XOR, self, self.__class__(other))
	
	def __mod__(self, other):
		return self.__class__(self.Mnemonic.MOD, self, self.__class__(other))
	
	def __getitem__(self, other):
		return self.__class__(self.Mnemonic.INDEX, self, self.__class__(other))
	
	def __bool__(self):
		try:
			e = self.evaluate()			
		except TypeError:
			pass
		else:
			if isinstance(e, bool):
				return e
			if isinstance(e, int):
				return bool(e)
		
		if not hasattr(self.__class__, 'conditions'):
			return False
		
		#if self.__mnemonic == self.Mnemonic.EQ and self.__operands[0].__mnemonic == self.Mnemonic.EQ:
		#	print("__bool__", self)
		#	raise RuntimeError
		
		if self not in self.conditions:
			raise ConditionError(self)
		else:
			return self.conditions[self]
	
	def __call__(self, *args):
		try:
			mnemonic = [self.Mnemonic.CALL0, self.Mnemonic.CALL1, self.Mnemonic.CALL2][len(args)]
		except IndexError:
			raise TypeError("Expected 0, 1 or 2 arguments.")
		return self.__class__(mnemonic, self, *[self.__class__(_arg) for _arg in args])
	
	def __gt__(self, other):
		return self.__class__(self.Mnemonic.GT, self, self.__class__(other))
	
	def __lt__(self, other):
		return self.__class__(self.Mnemonic.LT, self, self.__class__(other))
	
	def __ge__(self, other):
		return self.__class__(self.Mnemonic.GE, self, self.__class__(other))
	
	def __le__(self, other):
		return self.__class__(self.Mnemonic.LE, self, self.__class__(other))
	
	@classmethod
	def __tree_equals(cls, a, b):
		if a is b:
			return True
		
		if not isinstance(a, cls) and not isinstance(b, cls):
			return a == b
		
		if not isinstance(a, cls) or not isinstance(b, cls):
			return False
		
		return a.__mnemonic == b.__mnemonic and len(a.__operands) == len(b.__operands) and all(cls.__tree_equals(_a, _b) for (_a, _b) in zip(a.__operands, b.__operands))
	
	def __eq__(self, other):
		if self.__tree_equals(self, other):
			return True
		return self.__class__(self.Mnemonic.EQ, self, self.__class__(other))
	
	def __ne__(self, other):
		if self.__tree_equals(self, other):
			return False
		return self.__class__(self.Mnemonic.NE, self, self.__class__(other))
	
	def __hash__(self):
		return hash((self.__mnemonic,) + tuple(self.__operands))
	
	def sm_range(self):
		return self.__class__(self.Mnemonic.RANGE, self)
	
	def sm_length(self):
		try:
			return self.__length
		except AttributeError:
			raise TypeError("Could not evaluate symbolic length of SymbolicValue.")
	
	def __len__(self):
		try:
			return len(self.evaluate())
		except TypeError:
			try:
				return self.evaluate().type.pointee.count
			except AttributeError:
				raise TypeError("Could not evaluate length of SymbolicValue.")
	
	def __iter__(self):
		if hasattr(self.__class__, 'iter_counter'):
			iter_counter = self.__class__.iter_counter
			self.__class__.iter_counter += 1
			
			if self.__mnemonic == self.Mnemonic.RANGE:
				ff_pre = dict(stack()[1].frame.f_locals)
				print("iter vars pre:", list(ff_pre.keys()))

				#stack()[1].frame.update(ff_
				#PyFrame_LocalsToFast(py_object(ff), c_int(1))
				yield self.make_for(iter_counter)
				ff_post = dict(stack()[1].frame.f_locals)
				print("iter vars post:", list(ff_post.keys()))
				
				loop_vars = frozenset(ff_post.keys()) - frozenset(ff_pre.keys())
				static_vars = frozenset(k for k in (frozenset(ff_pre.keys()) & frozenset(ff_post.keys())) if ff_pre[k] is ff_post[k])
				dynamic_vars = (frozenset(ff_pre.keys()) | frozenset(ff_post.keys())) - loop_vars - static_vars
				print("loop vars:", loop_vars)
				print("static vars:", static_vars)
				print("dynamic vars:", dynamic_vars)
				
			else:
				yield self[self.make_for(iter_counter)]
		
		else:
			for n in range(len(self.evaluate())):
				yield n


class SymbolicArray(Array):
	StorageType = SymbolicValue
	Storage = SymbolicValue
	cast = SymbolicValue
	
	#def __getitem__(self, index):
	#	if not isinstance(index, int):
	#		raise RuntimeError
	#	else:
	#		return super().__getitem__(index)
	
	def sm_length(self):
		return self._Array__storage.sm_length()
	
	def __iter__(self):
		yield from self._Array__storage


class SymbolicField(BinaryGalois):
	field_power = SymbolicValue('Field.field_power')
	
	logarithm = SymbolicValue('Field.logarithm')
	exponent = SymbolicValue('Field.exponent')
	
	def serialize(self):
		yield self._BinaryGalois__value
	
	def __neg__(self, other):
		return SymbolicField(SymbolicValue('Field.__neg__')(list(self.serialize())[0]))
	
	def __add__(self, other):
		return SymbolicField(SymbolicValue('Field.__add__')(list(self.serialize())[0], list(other.serialize())[0]))
	
	def __sub__(self, other):
		return SymbolicField(SymbolicValue('Field.__sub__')(list(self.serialize())[0], list(other.serialize())[0]))
	
	def __mul__(self, other):
		return SymbolicField(SymbolicValue('Field.__mul__')(list(self.serialize())[0], list(other.serialize())[0]))
	
	def __truediv__(self, other):
		return SymbolicField(SymbolicValue('Field.__truediv__')(list(self.serialize())[0], list(other.serialize())[0]))
	
	def __pow__(self, other):
		return SymbolicField(SymbolicValue('Field.__pow__')(list(self.serialize())[0], other))
	
	def compile_(self, builder, args, iter_var, symbols, int_t):
		return SymbolicField(self._BinaryGalois__value.compile_(builder, args, iter_var, symbols, int_t))
	

class SymbolicLinear(Linear):
	def serialize(self):
		for f in self._Linear__f:
			yield from f.serialize()


class SymbolicQuadratic(Quadratic):
	def serialize(self):
		for f in self._Linear__f:
			yield from f.serialize()


def trace(fn):
	circuit = []
	
	def do_trace():
		try:
			SymbolicValue.iter_counter = 0
			result = fn()
		except ConditionError as e:
			ec = e.args[0]
			SymbolicValue.conditions[ec] = True
			do_trace()
			SymbolicValue.conditions[ec] = False
			do_trace()
			del SymbolicValue.conditions[ec]
			return
		except AssertionError:
			pass
		except (ArithmeticError, IndexError, AssertionError) as error:			
			if all(not _cond.contains_iter_stop() for _cond in SymbolicValue.conditions.keys()):
				circuit.append((dict(SymbolicValue.conditions), error.__class__.__name__ + ": " + str(error)))
		else:
			if result is NotImplemented:
				raise NotImplementedError
			elif hasattr(result, 'serialize'):
				circuit.append((dict(SymbolicValue.conditions), list(result.serialize())))
			else:
				circuit.append((dict(SymbolicValue.conditions), result))
	
	SymbolicValue.conditions = {}
	do_trace()
	del SymbolicValue.conditions, SymbolicValue.iter_counter
	
	return circuit


def compile_array(module, arr, name, int_t):
	table = llvmlite.ir.GlobalVariable(module, llvmlite.ir.ArrayType(int_t, len(arr)), name)
	table.initializer = llvmlite.ir.Constant(llvmlite.ir.ArrayType(int_t, len(arr)), [int_t(int(_n)) for _n in arr])
	table.global_constant = True
	return table


string_n = 0

def compile_string(module, string):
	global string_n
	table = llvmlite.ir.GlobalVariable(module, llvmlite.ir.ArrayType(char_t, len(string) + 1), f'.string_{string_n}')
	string_n += 1
	table.initializer = llvmlite.ir.Constant(llvmlite.ir.ArrayType(char_t, len(string) + 1), bytearray(string.encode('utf-8')) + bytearray([0]))
	table.global_constant = True
	table.linkage = 'internal'
	table.unnamed_addr = True
	return table


def compile_loop(fun, enter_block, exit_block, limits, n, loop_var, kernel, previous, int_t):
	if n >= len(limits):
		return kernel(enter_block, exit_block, loop_var, previous)
	
	iter_block = fun.append_basic_block()
	loop_block = fun.append_basic_block()
	inc_block = fun.append_basic_block()
	
	llvmlite.ir.IRBuilder(enter_block).branch(iter_block)
		
	builder = llvmlite.ir.IRBuilder(iter_block)
	i = builder.phi(int_t)
	loop_var.append(i)
	i.add_incoming(int_t(0), enter_block)	
	p = builder.phi(previous.type)
	p.add_incoming(previous, enter_block)
	builder.cbranch(builder.icmp_unsigned('<', i, int_t(limits[n])), loop_block, exit_block)
	
	result = compile_loop(fun, loop_block, inc_block, limits, n + 1, loop_var, kernel, p, int_t)
	
	builder = llvmlite.ir.IRBuilder(inc_block)
	i_inc = builder.add(i, int_t(1))
	builder.branch(iter_block)
	
	i.add_incoming(i_inc, inc_block)
	p.add_incoming(result, inc_block)
	
	return p


def compile_function(fun, symbols, circuit, int_t):
	return_type = fun.type.pointee.return_type
	
	enter_block = fun.append_basic_block()
	exit_block = fun.append_basic_block()
	
	def kernel(enter_block, exit_block, iter_var, data):
		return compile_kernel(fun, symbols, circuit, int_t, enter_block, exit_block, iter_var)
	
	loops = set()
	for conds, codes in circuit:
		for cond in conds.keys():
			loops.update(cond.extract_fors())
		
		if isinstance(codes, int) or isinstance(codes, str):
			continue
		
		loops.update(codes.extract_fors())
	
	print(len(loops), loops)
	
	result = compile_loop(fun, enter_block, exit_block, [999] * len(loops), 0, [], kernel, return_type(0), int_t) # FIXME
	
	llvmlite.ir.IRBuilder(exit_block).ret(result)


def compile_kernel(fun, symbols, circuit, int_t, enter_block, exit_block, iter_var):
	return_type = fun.type.pointee.return_type
	
	cond_block = fun.append_basic_block()
	llvmlite.ir.IRBuilder(enter_block).branch(cond_block)
	cond_builder = llvmlite.ir.IRBuilder(cond_block)
	
	return_block = fun.append_basic_block()
	return_builder = llvmlite.ir.IRBuilder(return_block)
	result = return_builder.phi(return_type)
	
	for conds, value in circuit:
		work_block = fun.append_basic_block()
		work_builder = llvmlite.ir.IRBuilder(work_block)
		
		ccs = []
		for c, v in conds.items():
			cc = c.compile_(cond_builder, fun.args, iter_var, symbols, int_t)
			if cc.type != bool_t:
				if v:
					cc = cond_builder.icmp_unsigned('!=', cc, cc.type(0))
				else:
					cc = cond_builder.icmp_unsigned('==', cc, cc.type(0))
			else:
				if not v:
					cc = cond_builder.not_(cc)
			ccs.append(cc)
		
		if len(ccs) == 0:
			cond_builder.branch(work_block)
			cond_block = fun.append_basic_block()
			cond_builder = llvmlite.ir.IRBuilder(cond_block)
		elif len(ccs) == 1:
			cond_block = fun.append_basic_block()
			cond_builder.cbranch(ccs[0], work_block, cond_block)
			cond_builder = llvmlite.ir.IRBuilder(cond_block)
		else:
			tc = ccs.pop()
			while ccs:
				td = ccs.pop()
				tc = cond_builder.and_(tc, td)
			cond_block = fun.append_basic_block()
			cond_builder.cbranch(tc, work_block, cond_block)
			cond_builder = llvmlite.ir.IRBuilder(cond_block)
		
		if not isinstance(value, str):
			if hasattr(return_type, 'pointee') and hasattr(return_type.pointee, 'count'):
				ret = work_builder.bitcast(work_builder.call(symbols['malloc'], [size_t(return_type.pointee.count)]), return_type)
				i = 0
				for rv in value:
					cv = rv.compile_(work_builder, fun.args, iter_var, symbols, int_t)
					if hasattr(cv, 'serialize'):
						for ncv in cv.serialize():
							work_builder.store(ncv, work_builder.gep(ret, [int_t(0), int_t(i)]))
							i += 1
					else:
						work_builder.store(cv, work_builder.gep(ret, [int_t(0), int_t(i)]))
						i += 1
				#work_builder.ret(ret)
				result.add_incoming(ret, work_block)
				work_builder.branch(return_block)
			elif isinstance(value, int):
				ret = return_type(value)
				#work_builder.ret(ret)
				result.add_incoming(ret, work_block)
				work_builder.branch(return_block)
			else:
				print("value:", repr(value))
				ret = work_builder.trunc(value.compile_(work_builder, fun.args, iter_var, symbols, int_t), return_type)
				#work_builder.ret(ret)
				result.add_incoming(ret, work_block)
				work_builder.branch(return_block)
		else:
			error_str = work_builder.bitcast(compile_string(fun.module, value), str_t)
			work_builder.call(symbols['error'], [error_str])
			ret = return_type(0)
			#work_builder.ret(return_type(0))
			result.add_incoming(ret, work_block)
			work_builder.branch(return_block)
	
	cond_builder.unreachable()
	return_builder.branch(exit_block)
	
	return result


void_t = llvmlite.ir.VoidType()
bool_t = llvmlite.ir.IntType(1)
char_t = llvmlite.ir.IntType(8)
str_t = char_t.as_pointer()
size_t = llvmlite.ir.IntType(64)


def compile_test(path):
	n_iters = 5
	
	short_t = llvmlite.ir.IntType(8)
	long_t = llvmlite.ir.IntType(16)
	array_short_t = llvmlite.ir.ArrayType(short_t, n_iters).as_pointer()
	
	module = llvmlite.ir.Module()
	
	symbols = {}
	symbols['error'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(void_t, [str_t]), 'error')
	symbols['malloc'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(str_t, [size_t]), 'malloc')
	symbols['pow'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(long_t, [long_t, long_t]), 'pow')
	
	n_iters_sym = llvmlite.ir.GlobalVariable(module, long_t, 'n_iters')
	n_iters_sym.initializer = llvmlite.ir.Constant(long_t, n_iters)
	n_iters_sym.global_constant = True
	symbols['n_iters'] = n_iters_sym
	
	def compile_scalar(fn):
		n = len(getfullargspec(fn).args)
		circuit = trace(lambda: fn(*[SymbolicValue.make_arg(_i) for _i in range(n)]))
		
		for cond, value in circuit:
			print(value, cond)
		print()
		
		fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t] * n), fn.__name__)
		compile_function(fun, symbols, circuit, long_t)
		return fn
	
	@compile_scalar
	def f_constant():
		return 77
	
	@compile_scalar
	def f_ignore(x):
		return 88
	
	@compile_scalar
	def f_identity(x):
		return x
	
	@compile_scalar
	def f_project(x, y):
		return y
	
	@compile_scalar
	def f_inc(x):
		return x + 1
	
	@compile_scalar
	def f_add(x, y):
		return x + y
	
	@compile_scalar
	def f_iter(x):
		r = 0
		for n, i in enumerate(sm_range(SymbolicValue(5))):
			r += i
		return r
	
	path.write_text(str(module) + "\n\n")


def compile_field(Field, path):
	short_t = llvmlite.ir.IntType(8)
	long_t = llvmlite.ir.IntType(16)
	
	module = llvmlite.ir.Module()
	
	symbols = {}
	symbols['error'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(void_t, [str_t]), 'error')
	symbols['Field.exponent'] = compile_array(module, Field.exponent, 'Field.exponent', short_t)
	symbols['Field.logarithm'] = compile_array(module, Field.logarithm, 'Field.logarithm', short_t)
	
	field_power = llvmlite.ir.GlobalVariable(module, long_t, 'Field.field_power')
	field_power = llvmlite.ir.Constant(long_t, Field.field_power)
	field_power.global_constant = True
	symbols['Field.field_power'] = field_power
	
	circuit = trace(lambda: Field.__neg__(SymbolicField(SymbolicValue('$0'))))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'Field.__neg__')
	compile_function(fun, symbols, circuit, long_t)
	
	circuit = trace(lambda: Field.__add__(SymbolicField(SymbolicValue('$0')), SymbolicField(SymbolicValue('$1'))))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'Field.__add__')
	compile_function(fun, symbols, circuit, long_t)
	
	circuit = trace(lambda: Field.__sub__(SymbolicField(SymbolicValue('$0')), SymbolicField(SymbolicValue('$1'))))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'Field.__sub__')
	compile_function(fun, symbols, circuit, long_t)
	
	circuit = trace(lambda: Field.__mul__(SymbolicField(SymbolicValue('$0')), SymbolicField(SymbolicValue('$1'))))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'Field.__mul__')
	compile_function(fun, symbols, circuit, long_t)
	
	circuit = trace(lambda: Field.__truediv__(SymbolicField(SymbolicValue('$0')), SymbolicField(SymbolicValue('$1'))))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'Field.__truediv__')
	compile_function(fun, symbols, circuit, long_t)
	
	circuit = trace(lambda: Field.__pow__(SymbolicField(SymbolicValue('$0')), SymbolicValue('$1')))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, long_t]), 'Field.__pow__')
	compile_function(fun, symbols, circuit, long_t)
	
	path.write_text(str(module) + "\n\n")


def compile_linear(field_power, path):
	short_t = llvmlite.ir.IntType(8)
	long_t = llvmlite.ir.IntType(16)
	array_short_t = llvmlite.ir.ArrayType(short_t, Field.field_power).as_pointer()
	
	module = llvmlite.ir.Module()
	
	symbols = {}
	symbols['malloc'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(str_t, [size_t]), 'malloc')
	symbols['error'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(void_t, [str_t]), 'error')
	symbols['pow'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(long_t, [long_t, long_t]), 'pow')
	symbols['Field.__neg__'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t]), 'Field.__neg__')
	symbols['Field.__add__'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'Field.__add__')
	symbols['Field.__sub__'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'Field.__sub__')
	symbols['Field.__mul__'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'Field.__mul__')
	symbols['Field.__pow__'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, long_t]), 'Field.__pow__')
	
	field_power = llvmlite.ir.GlobalVariable(module, long_t, 'Field.field_power')
	field_power.global_constant = True
	symbols['Field.field_power'] = field_power
	
	#a = lambda: SymbolicLinear(SymbolicArray([SymbolicValue('$0')[_i] for _i in sm_range(SymbolicField.field_power)], [None], [SymbolicField]))
	a = lambda: SymbolicLinear(SymbolicArray(SymbolicValue('$0', length=SymbolicField.field_power), [None], [SymbolicField]))
	b = lambda: SymbolicField(SymbolicValue('$1'))
	circuit = trace(lambda: Linear.__call__(a(), b()))
	
	for cond, val in circuit:
		print(val)
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [array_short_t, short_t]), 'Linear.__call__')
	compile_function(fun, symbols, circuit, long_t)
	
	#a = SymbolicLinear(SymbolicArray([SymbolicValue('$0')[_i] for _i in sm_range(SymbolicField.field_power)], [None], [SymbolicField]))
	#circuit = trace(lambda: Linear.__neg__(a))
	#fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(array_short_t, [array_short_t]), 'Linear.__neg__')
	#compile_function(fun, symbols, circuit, long_t)
	
	a = lambda: SymbolicLinear(SymbolicArray(SymbolicValue('$0', length=SymbolicField.field_power), [None], [SymbolicField]))
	b = lambda: SymbolicLinear(SymbolicArray(SymbolicValue('$1', length=SymbolicField.field_power), [None], [SymbolicField]))
	circuit = trace(lambda: Linear.__add__(a(), b()))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(array_short_t, [array_short_t, array_short_t]), 'Linear.__add__')
	compile_function(fun, symbols, circuit, long_t)
	
	'''
	a = lambda: SymbolicLinear(SymbolicArray([SymbolicValue('$0')[_i] for _i in sm_range(SymbolicField.field_power)], [None], [SymbolicField]))
	b = lambda: SymbolicLinear(SymbolicArray([SymbolicValue('$1')[_i] for _i in sm_range(SymbolicField.field_power)], [None], [SymbolicField]))
	circuit = trace(lambda: Linear.__sub__(a(), b()))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(array_short_t, [array_short_t, array_short_t]), 'Linear.__sub__')
	compile_function(fun, symbols, circuit, long_t)
	
	a = lambda: SymbolicLinear(SymbolicArray([SymbolicValue('$0')[_i] for _i in sm_range(SymbolicField.field_power)], [None], [SymbolicField]))
	b = lambda: SymbolicLinear(SymbolicArray([SymbolicValue('$1')[_i] for _i in sm_range(SymbolicField.field_power)], [None], [SymbolicField]))
	circuit = trace(lambda: Linear.__matmul__(a(), b()))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(array_short_t, [array_short_t, array_short_t]), 'Linear.__matmul__')
	compile_function(fun, symbols, circuit, long_t)
	
	a = lambda: SymbolicLinear(SymbolicArray([SymbolicValue('$0')[_i] for _i in sm_range(SymbolicField.field_power)], [None], [SymbolicField]))
	b = lambda: SymbolicField(SymbolicValue('$1'))
	circuit = trace(lambda: Linear.__mul__(a(), b()))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(array_short_t, [array_short_t, short_t]), 'Linear.__mul__')
	compile_function(fun, symbols, circuit, long_t)
	
	a = lambda: SymbolicLinear(SymbolicArray([SymbolicValue('$0')[_i] for _i in sm_range(SymbolicField.field_power)], [None], [SymbolicField]))
	b = lambda: SymbolicField(SymbolicValue('$1'))
	circuit = trace(lambda: Linear.__rmul__(a(), b()))
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(array_short_t, [array_short_t, short_t]), 'Linear.__rmul__')
	compile_function(fun, symbols, circuit, long_t)
	'''
	path.write_text(str(module) + "\n\n")




'''
if __name__ == '__main__':
	short_t = llvmlite.ir.IntType(8)
	long_t = llvmlite.ir.IntType(16)
	array_t = llvmlite.ir.ArrayType(llvmlite.ir.IntType(16), 8).as_pointer()
	
	module = llvmlite.ir.Module()
	
	fun = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(array_t, [array_t]), 'loop')
	ker = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(array_t, [array_t]), 'kernel')
	enter_block = fun.append_basic_block()
	exit_block = fun.append_basic_block()
	
	def kernel(block, loop_var, data):
		return llvmlite.ir.IRBuilder(block).call(ker, [data])
	
	r = create_loop(fun, enter_block, exit_block, [], 0, [], kernel, fun.args[0])
	
	llvmlite.ir.IRBuilder(exit_block).ret(r)
	
	print(module)
'''


if __name__ == '__main__':
	compile_test(Path('test.ll'))
	#Field = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	#compile_field(Field, Path('field.ll'))
	#compile_linear(Field.field_power, Path('linear.ll'))


