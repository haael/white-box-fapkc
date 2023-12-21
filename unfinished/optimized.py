#!/usr/bin/python3


from enum import Enum
from memory import *
from utils import sm_range


class Value:
	Mnemonic = Enum('Value.Mnemonic', 'CONST SYM FIELD RANGE ADD SUB MUL NEG POW')
	
	def __init__(self, mnemonic, *operands):
		try:
			self.__mnemonic = mnemonic.__mnemonic
			if hasattr(mnemonic, '_Value__operands'):
				self.__operands = mnemonic.__operands
			if hasattr(mnemonic, '_Value__value'):
				self.__value = mnemonic.__value
		except AttributeError:
			if isinstance(mnemonic, self.Mnemonic):
				self.__mnemonic = mnemonic
				if mnemonic in (self.Mnemonic.CONST, self.Mnemonic.SYM):
					self.__value = operands[0]
				else:
					self.__operands = operands
			else:
				if operands:
					raise TypeError
				self.__init__(self.Mnemonic.CONST, mnemonic)
	
	def __traverse(self, action):
		result = []
		stack = [self]
		indices = [0]
		
		while stack:
			try:
				branch = stack[-1]._Value__operands[indices[-1]]
			except (IndexError, TypeError, AttributeError):
				if isinstance(stack[-1], int):
					result.append(action(stack[-1]))
				elif hasattr(stack[-1], '_Value__value'):
					result.append(action(stack[-1]))
				elif stack[-1].__mnemonic in (self.Mnemonic.NEG, self.Mnemonic.FIELD, self.Mnemonic.RANGE):
					a = result.pop()
					result.append(action(stack[-1], a))
				else:
					a = result.pop()
					b = result.pop()
					result.append(action(stack[-1], b, a))
				
				stack.pop()
				indices.pop()
			else:
				stack.append(branch)
				indices[-1] += 1
				indices.append(0)
			
		assert len(result) == 1
		
		return result.pop()
	
	'''
	def compile(self, builder, funs):
		def action(node, x=None, y=None):
			if isinstance(node, int):
				return funs['int'](node)
			elif node.__mnemonic == self.Mnemonic.CONST:
				return funs['const'](node.__value)
			elif node.__mnemonic == self.Mnemonic.SYM:
				return funs['sym'](node.__value)
			elif node.__mnemonic == self.Mnemonic.NEG:
				return builder.call(funs['neg'], [x])
			elif node.__mnemonic == self.Mnemonic.ADD:
				return builder.call(funs['add'], [x, y])
			elif node.__mnemonic == self.Mnemonic.SUB:
				return builder.call(funs['sub'], [x, y])
			elif node.__mnemonic == self.Mnemonic.MUL:
				return builder.call(funs['mul'], [x, y])
			elif node.__mnemonic == self.Mnemonic.POW:
				return builder.call(funs['pow'], [x, y])
			else:
				raise NotImplementedError
		
		return self.__traverse(action)
	'''
	
	def evaluate(self, Field):
		def action(node, x=None, y=None):
			if isinstance(node, int):
				return node
			elif node.__mnemonic == self.Mnemonic.CONST:
				return self.__value
			elif node.__mnemonic == self.Mnemonic.SYM:
				raise ValueError(f"Symbolic variable {node.__value} can not be evaluated.")
			elif node.__mnemonic == self.Mnemonic.FIELD:
				return Field(x)
			elif node.__mnemonic == self.Mnemonic.NEG:
				return -x
			elif node.__mnemonic == self.Mnemonic.ADD:
				return x + y
			elif node.__mnemonic == self.Mnemonic.SUB:
				return x - y
			elif node.__mnemonic == self.Mnemonic.MUL:
				return x * y
			elif node.__mnemonic == self.Mnemonic.POW:
				return x ** y
			else:
				raise NotImplementedError
		
		return self.__traverse(action)
	
	def __str__(self):
		def action(node, x=None, y=None):
			if isinstance(node, int):
				return str(node)
			elif hasattr(node, '_Value__value'):
				return f"{node.__mnemonic.name}({str(node.__value)})"
			elif node.__mnemonic == self.Mnemonic.NEG:
				return f"NEG({x})"
			else:
				return f"{node.__mnemonic.name}({x}, {y})"
		
		return self.__traverse(action)
	
	def __add__(self, other):
		return self.__class__(self.Mnemonic.ADD, self, other)
	
	def __radd__(self, other):
		return self.__class__(self.Mnemonic.ADD, other, self)
	
	def __sub__(self, other):
		return self.__class__(self.Mnemonic.SUB, self, other)
	
	def __rsub__(self, other):
		return self.__class__(self.Mnemonic.SUB, other, self)
	
	def __mul__(self, other):
		return self.__class__(self.Mnemonic.MUL, self, other)
	
	def __rmul__(self, other):
		return self.__class__(self.Mnemonic.MUL, other, self)
	
	def __neg__(self, other):
		return self.__class__(self.Mnemonic.NEG, self)
	
	def __pow__(self, other):
		return self.__class__(self.Mnemonic.POW, self, other)
	
	def sm_range(self):
		if self.__mnemonic == self.Mnemonic.CONST:
			yield self.__value
		else:
			yield self.__class__(self.Mnemonic.RANGE, self)
	
	def __eq__(self, other):
		try:
			if self.__mnemonic != other.__mnemonic:
				return False
		except AttributeError:
			return NotImplemented
		
		if hasattr(self, '_Value__value') and hasattr(other, '_Value__value'):
			return self.__value == other.__value
		elif hasattr(self, '_Value__operands') and hasattr(other, '_Value__operands'):
			return self.__operands == other.__operands
		else:
			return False
	
	def __hash__(self):
		if hasattr(self, '_Value__value'):
			return hash((self.__mnemonic, self.__value))
		elif hasattr(self, '_Value__operands'):
			return hash((self.__mnemonic,) + tuple(self.__operands))
		else:
			raise NotImplementedError



class SymbolicArray(Array):
	StorageType = list
	Storage = list
	cast = lambda x: x
	
	def __getitem__(self, key):
		print("getitem", key)
		#if isinstance(key, int):
		#	return super().__getitem__(key)
		#else:
		return SymbolicField(Value.Mnemonic.FIELD, Value(Value.Mnemonic.SYM, f'SA_{str(key)}'))
		#print("getitem", key)
		#raise RuntimeError


class SymbolicTable(Table):
	StorageType = list
	Storage = list
	cast = lambda x: x


if __debug__ and __name__ == '__main__':
	from linear import *
	from machines import *
	import llvmlite.ir
	from fields import Galois
	
	Field = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	
	random_serial = 0
	
	class SymbolicField(Value):
		field_base = Field.field_base
		field_power = Field.field_power
		field_size = field_base ** field_power
		
		@classmethod
		@property
		def Field(cls):
			return cls
		
		@classmethod
		def random(cls, randbelow):
			global random_serial
			r = random_serial
			random_serial += 1
			return cls(Value.Mnemonic.FIELD, cls(Value.Mnemonic.SYM, f'r_{r}'))	
	
	
	module = llvmlite.ir.Module()
	short_t = llvmlite.ir.IntType(8) # type for field element representation
	long_t =  llvmlite.ir.IntType(16) # type for arithmetics
	
	exp_table = llvmlite.ir.GlobalVariable(module, llvmlite.ir.ArrayType(short_t, Field.field_size), 'exp')
	exp_table.initializer = llvmlite.ir.Constant(llvmlite.ir.ArrayType(short_t, Field.field_size), [short_t(int(_n)) for _n in Field.exponent])
	exp_table.global_constant = True
	log_table = llvmlite.ir.GlobalVariable(module, llvmlite.ir.ArrayType(short_t, Field.field_size), 'log')
	log_table.initializer = llvmlite.ir.Constant(llvmlite.ir.ArrayType(short_t, Field.field_size), [short_t(int(_n)) for _n in Field.logarithm])
	log_table.global_constant = True
	
	funs = {}
	funs['int'] = long_t
	funs['const'] = short_t
	
	# Galois field negation
	funs['neg'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t]), 'neg')
	block = funs['neg'].append_basic_block()
	builder = llvmlite.ir.IRBuilder(block)
	builder.ret(funs['neg'].args[0])
	
	# Galois field summation
	funs['add'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'add')
	block = funs['add'].append_basic_block()
	builder = llvmlite.ir.IRBuilder(block)
	result = builder.xor(funs['add'].args[0], funs['add'].args[1])
	builder.ret(result)
	
	# Galois field subtraction
	funs['sub'] = funs['add']
	
	# Galois field multiplication
	funs['mul'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, short_t]), 'mul')
	a1_block = funs['mul'].append_basic_block()
	a2_block = funs['mul'].append_basic_block()
	z_block = funs['mul'].append_basic_block()
	n_block = funs['mul'].append_basic_block()
	
	builder = llvmlite.ir.IRBuilder(z_block)
	builder.ret(short_t(0))
	
	builder = llvmlite.ir.IRBuilder(a1_block)
	v0 = funs['mul'].args[0]
	v0s = builder.icmp_unsigned('==', v0, short_t(0))
	builder.cbranch(v0s, z_block, a2_block)
	
	builder = llvmlite.ir.IRBuilder(a2_block)
	v1 = funs['mul'].args[1]
	v1s = builder.icmp_unsigned('==', v1, short_t(0))
	builder.cbranch(v1s, z_block, n_block)
	
	builder = llvmlite.ir.IRBuilder(n_block)
	v2 = builder.load(builder.gep(log_table, [long_t(0), builder.zext(v0, long_t)]))
	v3 = builder.zext(v2, long_t)
	v4 = builder.load(builder.gep(log_table, [long_t(0), builder.zext(v1, long_t)]))
	v5 = builder.zext(v4, long_t)
	v6 = builder.add(v3, v5)
	v7 = builder.urem(v6, long_t(Field.field_size - 1))
	v8 = builder.trunc(v7, short_t)
	v9 = builder.load(builder.gep(exp_table, [long_t(0), builder.zext(v8, long_t)]))
	builder.ret(v9)
	
	# Galois field exponentiation
	funs['pow'] = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(short_t, [short_t, long_t]), 'pow')
	a_block = funs['pow'].append_basic_block()
	z_block = funs['pow'].append_basic_block()
	n_block = funs['pow'].append_basic_block()
	
	builder = llvmlite.ir.IRBuilder(z_block)
	builder.ret(short_t(0))
	
	builder = llvmlite.ir.IRBuilder(a_block)
	v0 = funs['pow'].args[0]
	v0s = builder.icmp_unsigned('==', v0, short_t(0))
	builder.cbranch(v0s, z_block, n_block)
	
	builder = llvmlite.ir.IRBuilder(n_block)
	v1 = builder.load(builder.gep(log_table, [long_t(0), builder.zext(v0, long_t)]))
	v2 = builder.zext(v1, long_t)
	v3 = builder.add(v2, funs['pow'].args[1])
	v4 = builder.srem(v3, long_t(Field.field_size - 1))
	v5 = builder.trunc(v4, short_t)
	v6 = builder.load(builder.gep(exp_table, [long_t(0), builder.zext(v5, long_t)]))
	builder.ret(v6)
	
	#print(str(module))
	
	output_size = Value(Value.Mnemonic.SYM, 'output_len')
	input_size = Value(Value.Mnemonic.SYM, 'input_len')
	state_size = Value(Value.Mnemonic.SYM, 'state_len')
	

	out_transition = QuadraticCircuit.random(output_size, input_size + state_size, SymbolicTable, SymbolicArray, Quadratic, Linear, SymbolicField, None)
	state_transition = QuadraticCircuit.random(state_size, input_size + state_size, SymbolicTable, SymbolicArray, Quadratic, Linear, SymbolicField, None)
	init_state = Vector.random(state_size, SymbolicArray, SymbolicField, None)
	automaton = Automaton(out_transition, state_transition, init_state)


	#automaton = Automaton.random_quadratic_quadratic(output_len, input_len, state_len, SymbolicTable, SymbolicArray, Vector, QuadraticCircuit, Quadratic, Linear, SymbolicField, None)
	state = Vector(SymbolicArray([SymbolicField(Value.Mnemonic.SYM, f's_{_n}') for _n in sm_range(state_size)], [None], [SymbolicField]))
	def symbolic_stream():
		yield Vector(SymbolicArray([SymbolicField(Value.Mnemonic.SYM, f'i_{_n}') for _n in sm_range(input_size)], [None], [SymbolicField]))	
	result = list(automaton(symbolic_stream(), state))[0]
	
	#print(state)
	
	ot_table = llvmlite.ir.GlobalVariable(module, llvmlite.ir.ArrayType(short_t, len(automaton.out_transition.serialize())), 'output_transition')
	ot_table.global_constant = True
	#ot_table.initializer = automaton.out_transition.serialize()
	st_table = llvmlite.ir.GlobalVariable(module, llvmlite.ir.ArrayType(short_t, len(automaton.state_transition.serialize())), 'state_transition')
	st_table.global_constant = True
	#st_table.initializer = automaton.state_transition.serialize()
	
	step = llvmlite.ir.Function(module, llvmlite.ir.FunctionType(llvmlite.ir.VoidType(), [llvmlite.ir.ArrayType(short_t, output_len).as_pointer(), llvmlite.ir.ArrayType(short_t, input_len).as_pointer(), llvmlite.ir.ArrayType(short_t, state_len).as_pointer()]), 'step')
	block = step.append_basic_block()
	
	builder = llvmlite.ir.IRBuilder(block)
	
	input_syms = dict((f'i_{_n}', builder.load(builder.gep(step.args[1], [long_t(0), long_t(_n)]))) for _n in range(input_len))
	state_syms = dict((f's_{_n}', builder.load(builder.gep(step.args[2], [long_t(0), long_t(_n)]))) for _n in range(state_len))
	
	#output_trans = dict((_v._Value__value, builder.load(builder.gep(ot_table, [long_t(0), long_t(_n)]))) for (_n, _v) in enumerate(automaton.out_transition.serialize()))
	#state_trans = dict((_v._Value__value, builder.load(builder.gep(st_table, [long_t(0), long_t(_n)]))) for (_n, _v) in enumerate(automaton.state_transition.serialize()))
	
	def sym(s):
		if s in input_syms:
			return input_syms[s]
		elif s in state_syms:
			return state_syms[s]
		elif s in output_trans:
			return output_trans[s]
		elif s in state_trans:
			return state_trans[s]
		else:
			raise KeyError(f"Symbol not found: {s}.")
	
	funs['sym'] = sym
	
	#for n in range(output_len):
	#	builder.store(result[n].compile(builder, funs), builder.gep(step.args[0], [long_t(0), long_t(n)]))
	
	#for n in range(state_len):
	#	builder.store(state[n].compile(builder, funs), builder.gep(step.args[2], [long_t(0), long_t(n)]))
	
	print(str(module))
