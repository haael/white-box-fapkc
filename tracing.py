#!/usr/bin/python3


import inspect
import ast
from enum import Enum
from ctypes import py_object, c_int, pythonapi
from llvmlite.ir import VoidType, IntType, ArrayType, FunctionType, Constant, GlobalVariable, Function, Module, IRBuilder
from collections import defaultdict


class MissingCondition(BaseException):
	pass


class NonConstantExpression(Exception):
	pass


class SymbolicValue:
	Mnemonic = Enum('SymbolicValue.Mnemonic', 'CONST LIST ARG FOR IF LOOP CALL INDEX ADD SUB MUL FLOORDIV MOD NEG POW SHL XOR AND EQ NE GT GE LT LE')
	
	def __init__(self, value, *operands):
		if not operands:
			if isinstance(value, self.Mnemonic):
				raise TypeError(f"Missing operands: {value}")
			
			try:
				self.__mnemonic = value.__mnemonic
				self.__operands = value.__operands
			except AttributeError:
				if isinstance(value, list) or isinstance(value, tuple):
					self.__mnemonic = self.Mnemonic.LIST
					self.__operands = [self.__class__(_element) for _element in value]
				else:
					self.__mnemonic = self.Mnemonic.CONST
					self.__operands = [value]
		else:
			self.__mnemonic = value
			self.__operands = operands
		
		if not isinstance(self.__operands, (list, tuple)):
			raise TypeError(f"Operands type is {type(self.__operands).__name__}")
		
		if self.__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR]:
			if any(not isinstance(_operand, self.__class__) for _operand in self.__operands):
				raise TypeError("All operands must be SymbolicValue.")
	
	@classmethod
	def make_const(cls, c):
		return cls(cls.Mnemonic.CONST, c)
	
	@classmethod
	def make_list(cls, *l):
		return cls(cls.Mnemonic.LIST, *[cls(_el) for _el in l])
	
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
	
	@classmethod
	def make_if(cls, cond, yes, no):
		return cls(cls.Mnemonic.IF, *[cls(_el) for _el in [cond, yes, no]])
	
	@classmethod
	def make_loop(cls, args, result, init, count):
		return cls(cls.Mnemonic.LOOP, *[cls(_el) for _el in [args, result, init, count]])
	
	def __traverse(self, action):
		if self.__mnemonic in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR]:
			return action(self)
		else:
			return action(self, *[_op.__traverse(action) for _op in self.__operands])
	
	def substitute(self, from_, to):
		def action(node, *args):
			for n, f in enumerate(from_):
				if self.__tree_equals(f, node):
					return to[n]
			else:
				if node.__mnemonic in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR]:
					return node
				else:
					return self.__class__(node.__mnemonic, *args)
		
		return self.__traverse(action)
	
	def evaluate(self):
		def pre_action(node, *args):
			if node.__mnemonic == self.Mnemonic.ARG:
				raise NonConstantExpression(node)
			elif node.__mnemonic == self.Mnemonic.FOR:
				return node
			elif node.__mnemonic == self.Mnemonic.INDEX:
				x, y = args
				try:
					return x[y]
				except IndexError:
					return None
			else:
				return self.__eval_action(node, *args)
		
		def post_action(node, *args):
			if node.__mnemonic == self.Mnemonic.ARG:
				raise NonConstantExpression(node)
			elif node.__mnemonic == self.Mnemonic.FOR:
				return node
			else:
				return self.__eval_action(node, *args)
		
		return self.__class__(self.__traverse(pre_action)).__traverse(post_action)
	
	def simplify(self):
		def action(node, *args):
			if node.__mnemonic == self.Mnemonic.ARG or node.__mnemonic == self.Mnemonic.FOR:
				return node
			else:
				return self.__eval_action(node, *args)
		
		return self.__traverse(action)
	
	def compile(self, function, long_t, symbols):
		builder_number = 0
		for_var = {}
		loops = {}
		node_serial = 0
		
		before_loop = defaultdict(list)
		after_loop = defaultdict(list)
		begin_loop = defaultdict(list)
		end_loop = defaultdict(list)
		
		begin_index = defaultdict(list)
		end_index = defaultdict(list)
		
		def create_builder():
			nonlocal builder_number
			block = function.append_basic_block()
			builder = IRBuilder(block)
			number = builder_number
			builder_number += 1
			return block, builder, number
		
		def first_builder(*builders):
			return sorted(builders, key=lambda _x: _x[2])[0]
		
		def last_builder(*builders):
			return sorted(builders, key=lambda _x: _x[2])[-1]
		
		def not_terminated(fn):
			def new_fn(node, block, builder, number):
				assert not block.is_terminated
				rvalue, rblock, rbuilder, rnumber = fn(node, block, builder, number)
				#assert block.is_terminated if (node.__mnemonic != self.Mnemonic.LOOP) else not block.is_terminated, f"not terminated: {node.__mnemonic}"
				assert not rblock.is_terminated, f"terminated: {node.__mnemonic}, {node}"
				return rvalue, rblock, rbuilder, rnumber
			return new_fn
		
		@not_terminated
		def build(node, block, builder, number):
			nonlocal node_serial
			#print(node.__mnemonic, id(node), node)
			
			if node.__mnemonic == self.Mnemonic.IF:
				cond, yes, no = node.__operands
				
				cond_result, cond_block, cond_builder, cond_number = build(cond, block, builder, number)
				
				yes_block, yes_builder, yes_number = create_builder()
				no_block, no_builder, no_number = create_builder()
				
				cond_builder.comment(f"if ({str(cond)})")
				cond_builder.cbranch(cond_result, yes_block, no_block)
				
				yes_result, yes_block, yes_builder, yes_number = build(yes, yes_block, yes_builder, yes_number)
				no_result, no_block, no_builder, no_number = build(no, no_block, no_builder, no_number)
				
				join_block, join_builder, join_number = create_builder()
				yes_builder.branch(join_block)
				no_builder.branch(join_block)
				
				result = join_builder.phi(long_t)
				result.add_incoming(yes_result, yes_block)
				result.add_incoming(no_result, no_block)
				
				return result, join_block, join_builder, join_number
			
			elif node.__mnemonic == self.Mnemonic.LOOP:
				try:
					lb = loops[node]
				except KeyError:
					pass
				else:
					builder.comment(f"before loop {hex(hash(node))}")
					before_loop[node].append((block, builder, number))
					block, builder, number = create_builder()
					builder.comment(f"after loop {hex(hash(node))}")
					after_loop[node].append((block, builder, number))
					return lb, block, builder, number
				
				builder.comment(f"before loop {hex(hash(node))}")
				before_loop[node].append((block, builder, number))
				#orig_block, orig_builder, orig_number = block, builder, number
				
				block, builder, number = create_builder()
				#start_block, start_builder, start_number = block, builder, number
				builder.comment(f"begin loop {hex(hash(node))}")
				begin_loop[node].append((block, builder, number))
				
				fors, result, init, count = node.__operands
				fors = fors.__operands
				result = result.__operands
				init = init.__operands
				
				r_count, block, builder, number = build(count, block, builder, number)
				
				r_init = []
				for item in init:
					value, block, builder, number = build(item, block, builder, number)
					r_init.append(value)
				
				init_block = block
				init_builder = builder
				
				block, builder, number = create_builder()
				test_block = block
				test_builder = builder
				
				init_builder.branch(test_block)
				
				r_var = []
				for n, rv in enumerate(fors):
					fv = for_var[rv.__operands[0]] = builder.phi(long_t)
					fv.add_incoming(r_init[n], init_block)
					r_var.append(fv)
				
				block, builder, number = create_builder()
				body_block = block
				
				r_result = []
				for item in result:
					value, block, builder, number = build(item, block, builder, number)
					r_result.append(value)
				for n, rr in enumerate(r_result):
					r_var[n].add_incoming(rr, block)
				builder.branch(test_block)
				
				block, builder, number = create_builder()
				exit_block = block
				
				test_builder.comment(f"cond loop {fors[0]} < {count}")
				test_builder.cbranch(test_builder.icmp_signed('<', r_var[0], r_count), body_block, exit_block)
				
				loops[node] = r_var
				builder.comment(f"end loop {hex(hash(node))}")
				end_loop[node].append((block, builder, number))
				
				block, builder, number = create_builder()
				builder.comment(f"after loop {hex(hash(node))}")
				after_loop[node].append((block, builder, number))
				
				return r_var, block, builder, number
			
			elif node.__mnemonic == self.Mnemonic.ARG:
				return builder.sext(function.args[node.__operands[0]], long_t), block, builder, number
			
			elif node.__mnemonic == self.Mnemonic.FOR:
				return for_var[node.__operands[0]] if node.__operands[0] in for_var else long_t(0), block, builder, number
			
			elif node.__mnemonic == self.Mnemonic.CONST:
				return long_t(int(node.__operands[0])), block, builder, number
			
			elif node.__mnemonic == self.Mnemonic.LIST:
				result = []
				builders = []
				for item in node.__operands:
					value, block, builder, number = build(item, block, builder, number)
					result.append(value)
					builders.append((block, builder, number))
				block, builder, number = last_builder(*builders)
				return result, block, builder, number
			
			elif node.__mnemonic == self.Mnemonic.INDEX:
				#enter_block, enter_builder, enter_number = block, builder, number
				
				index_serial = node_serial
				node_serial += 1
				
				builder.comment(f"begin index {hex(hash(node))}")
				begin_index[index_serial].append((block, builder, number))
				
				list_, list_block, list_builder, list_number = build(node.__operands[0], block, builder, number)
				
				index, index_block, index_builder, index_number = build(node.__operands[1], list_block, list_builder, list_number)
				
				if isinstance(index, Constant):
					block, builder, number = last_builder((list_block, list_builder, list_number), (index_block, index_builder, index_number))
					builder.comment(f"end index (const: {index.constant}) {hex(hash(node))}")
					end_index[index_serial].append((block, builder, number))
					return list_[index.constant] if (0 <= index.constant < len(list_)) else long_t(0), block, builder, number
				
				else:
					block, builder, number = last_builder((list_block, list_builder, list_number), (index_block, index_builder, index_number))
					
					test_block = [block]
					test_builder = [builder]
					for n in range(len(list_)):
						block, builder, number = create_builder()
						test_block.append(block)
						test_builder.append(builder)
					join_block, join_builder, join_number = create_builder()
					
					phi = join_builder.phi(long_t)
					
					for n in range(len(list_)):
						test_builder[n].comment(f"check index {node.__operands[1]} == {n}")
						test_builder[n].cbranch(test_builder[n].icmp_signed('==', index, long_t(n)), join_block, test_block[n + 1])
						phi.add_incoming(list_[n], test_block[n])
					test_builder[-1].branch(join_block)
					phi.add_incoming(long_t(0), test_block[-1])
					
					join_builder.comment(f"end index (var: {node.__operands[1]}) {hex(hash(node))}")
					end_index[index_serial].append((join_block, join_builder, join_number))
					return phi, join_block, join_builder, join_number
			
			elif node.__mnemonic == self.Mnemonic.CALL:
				f, *args = node.__operands
				fn = symbols[f.__name__]
				
				a = []
				builders = []
				nbuilder = block, builder, number
				for n, arg in enumerate(args):
					value, nbuilder = build(node, *nbuilder)
					a.append(value)
					builders.append(nbuilder)
				
				block, builder, number = last_builder(*builders)
				ar = [builder.trunc(_a, _t.type) for (_a, _t) in zip(a, fn.args)]
				return builder.call(fn, ar), block, builder, number
			
			elif node.__mnemonic == self.Mnemonic.NEG:
				x, block, builder, number = build(node.__operands[0], block, builder, number)
				return builder.neg(x), block, builder, number
			elif node.__mnemonic == self.Mnemonic.ADD:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.add(x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.SUB:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.sub(x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.MUL:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.mul(x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.FLOORDIV:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				xmy = builder.icmp_signed('!=', builder.srem(x, y), long_t(0))
				xl0 = builder.icmp_signed('<', x, long_t(0))
				yl0 = builder.icmp_signed('<', y, long_t(0))
				xl0_xor_yl0 = builder.xor(xl0, yl0)
				xmy_and_xxy = builder.and_(xmy, xl0_xor_yl0)
				d = builder.sdiv(x, y)
				d_minus_1 = builder.sub(d, long_t(1))
				r = builder.select(xmy_and_xxy, d_minus_1, d)
				return r, block, builder, number
			elif node.__mnemonic == self.Mnemonic.POW:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.call(symbols['_pow'], [x, y]), block, builder, number
			elif node.__mnemonic == self.Mnemonic.SHL:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.shl(x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.XOR:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.xor(x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.AND:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.and_(x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.MOD:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.urem(x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.GT:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.icmp_signed('>', x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.GE:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.icmp_signed('>=', x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.LT:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.icmp_signed('<', x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.LE:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.icmp_signed('<=', x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.EQ:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.icmp_signed('==', x, y), block, builder, number
			elif node.__mnemonic == self.Mnemonic.NE:
				x, block1, builder1, number1 = build(node.__operands[0], block, builder, number)
				y, block2, builder2, number2 = build(node.__operands[1], block1, builder1, number1)
				block, builder, number = last_builder((block1, builder1, number1), (block2, builder2, number2))
				return builder.icmp_signed('!=', x, y), block, builder, number
			else:
				raise NotImplementedError
		
		block, builder, number = create_builder()
		result, block, builder, number = build(self, block, builder, number)
		builder.ret(builder.trunc(result, function.type.pointee.return_type))
		
		for loop, builders in before_loop.items():
			block, builder, number = first_builder(*builders)
			try:
				index = [_index for (_index, _builders) in begin_index.items() if number in frozenset(_bb[2] for _bb in _builders)][0]
			except IndexError:
				builder.branch(begin_loop[loop][0])
			else:
				assert len(begin_index[index]) == 1
				begin_index[index][0][1].branch(begin_loop[loop][0][0])
				end_loop[loop][0][1].branch(after_loop[loop][0][0])
		
		for index, builders in begin_index.items():
			assert len(builders) == 1
			block, builder, number = builders[0]
			if block.is_terminated: continue
			builder.branch(end_index[index][0][0])
		
		for index, builders in begin_index.items():
			(block, builder, number) = builders[0]
			assert block.is_terminated
	
	@classmethod
	def __eval_action(cls, node, *args):
		if node.__mnemonic == cls.Mnemonic.CONST:
			return node.__operands[0]
		elif node.__mnemonic == cls.Mnemonic.LIST:
			return args
		elif node.__mnemonic == cls.Mnemonic.CALL:
			x, *r = args
			return x(*r)
		elif node.__mnemonic == cls.Mnemonic.IF:
			cond, yes, no = args
			if isinstance(cond, cls):
				return cls.make_if(cond, yes, no)
			elif cond:
				return yes
			else:
				return no
		elif node.__mnemonic == cls.Mnemonic.LOOP:
			fors, result, init, count = args
			
			if isinstance(count, cls):
				return cls.make_loop(fors, result, init, count)
			
			result = [_element for _element in cls(result).__operands]
			data = [cls(_element).simplify() for _element in init]
			
			assert len(data) == len(result)
			
			while count > 0:
				n = 0
				nzfor, nzdata = zip(*[(_for, cls(_delement)) for (_for, _delement) in zip(fors, data) if _for != None])
				assert not any(_d == None for _d in nzdata)
				
				while n < len(result):
					if fors[n] != None:
						assert result[n] != None
						data[n] = cls(result[n].substitute(nzfor, nzdata).simplify())
					n += 1
				count -= 1
			
			if any(isinstance(_element, cls) for _element in data):
				return cls.make_list(*data)
			else:
				return data
		elif node.__mnemonic == cls.Mnemonic.INDEX:
			x, y = args
			try:
				return x[y]
			except IndexError:
				raise IndexError(f"Out of range: `{x}[{y}]`.")
		elif node.__mnemonic == cls.Mnemonic.NEG:
			x, = args
			return -x
		elif node.__mnemonic == cls.Mnemonic.ADD:
			x, y = args
			return x + y
		elif node.__mnemonic == cls.Mnemonic.SUB:
			x, y = args
			return x - y
		elif node.__mnemonic == cls.Mnemonic.MUL:
			x, y = args
			return x * y
		elif node.__mnemonic == cls.Mnemonic.FLOORDIV:
			x, y = args
			return x // y
		elif node.__mnemonic == cls.Mnemonic.POW:
			x, y = args
			return x ** y
		elif node.__mnemonic == cls.Mnemonic.SHL:
			x, y = args
			return x << y
		elif node.__mnemonic == cls.Mnemonic.XOR:
			x, y = args
			return x ^ y
		elif node.__mnemonic == cls.Mnemonic.AND:
			x, y = args
			return x & y
		elif node.__mnemonic == cls.Mnemonic.MOD:
			x, y = args
			return x % y
		elif node.__mnemonic == cls.Mnemonic.GT:
			x, y = args
			return x > y
		elif node.__mnemonic == cls.Mnemonic.GE:
			x, y = args
			return x >= y
		elif node.__mnemonic == cls.Mnemonic.LT:
			x, y = args
			return x < y
		elif node.__mnemonic == cls.Mnemonic.LE:
			x, y = args
			return x <= y
		elif node.__mnemonic == cls.Mnemonic.EQ:
			x, y = args
			return x == y
		elif node.__mnemonic == cls.Mnemonic.NE:
			x, y = args
			return x != y
		else:
			raise NotImplementedError(f"Could not evaluate: {node.__mnemonic.name}")
	
	def extract_args(self):
		def action(node, *args):
			if node.__mnemonic == self.Mnemonic.ARG:
				return frozenset([node])
			else:
				return frozenset().union(*args)
		
		return self.__traverse(action)
	
	def extract_fors(self):
		def action(node, *args):
			if node.__mnemonic == self.Mnemonic.FOR:
				return frozenset([node])
			else:
				return self.__class__(node.__mnemonic, *args)
		
		return self.__traverse(action)
	
	def optimize_loops(self):
		def action(node, *args):
			if node.__mnemonic in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR]:
				return node
			elif node.__mnemonic == self.Mnemonic.INDEX:
				list_, index = args
				if list_.__mnemonic == self.Mnemonic.LOOP:
					count = list_.__operands[3]
					fors, result, init = map((lambda _x: list(_x.__operands)), list_.__operands[:3])
					
					assert len(fors) == len(result) == len(init)
					
					index = index.simplify()
					
					if isinstance(index, self.__class__):
						orig_init = list(init)
						orig_fors = list(fors)
						for n in reversed([_n for (_n, _f) in enumerate(list(fors)) if _f == None]):
							del fors[n], result[n], init[n]
						loop = self.make_loop(fors, result, init, count)
						
						case_ = SymbolicValue(0)
						less = 0
						for n in range(len(orig_fors)):
							if orig_fors[n] == None:
								case_ = self.make_if(index == n, orig_init[n], case_)
								less += 1
							else:
								case_ = self.make_if(index == n, loop[index - less], case_)
						
						return case_
					elif fors[index] == None:
						return init[index]
					else:
						for n in reversed([_n for (_n, _f) in enumerate(list(fors)) if _f == None]):
							del fors[n], result[n], init[n]
							if n <= index:
								index -= 1
						return self.make_loop(fors, result, init, count)[index]
				
				elif list_.__mnemonic == self.Mnemonic.IF:
					cond, yes, no = list_.__operands
					return self.make_if(cond, yes[index].optimize_loops(), no[index].optimize_loops())
				else:
					return self.__class__(node.__mnemonic, *args)
			elif node.__mnemonic == self.Mnemonic.LOOP:
				count = args[3]
				fors, result, init = map((lambda _x: list(_x.__operands)), args[:3])
				static_vars = [(_n, _f, _i) for (_n, (_f, _r, _i)) in enumerate(zip(fors, result, init)) if self.__tree_equals(_f, _r)]
				if not static_vars:
					return self.__class__(node.__mnemonic, *args)
				
				num, from_, to = zip(*static_vars)
				
				for n in num:
					fors[n] = None
				
				result = self.make_list(*result).substitute(from_, to)
				new_loop = self.make_loop(fors, result, init, count)
				return new_loop
			else:
				return self.__class__(node.__mnemonic, *args)
		
		return self.__traverse(action)
	
	def __str__(self):
		def action(node, *args):
			if node.__mnemonic == self.Mnemonic.CONST:
				if hasattr(node.__operands[0], '__name__'):
					return node.__operands[0].__name__
				else:
					return str(node.__operands[0])
			elif node.__mnemonic == self.Mnemonic.LIST:
				return '[' + ', '.join(str(_op) for _op in args) + ']'
			elif node.__mnemonic == self.Mnemonic.IF:
				return 'if(' + ', '.join(args) + ')'
			elif node.__mnemonic == self.Mnemonic.LOOP:
				return 'loop(' + ', '.join(args) + ')'
			elif node.__mnemonic == self.Mnemonic.ARG:
				return '$' + str(node.__operands[0])
			elif node.__mnemonic == self.Mnemonic.FOR:
				return '£' + str(node.__operands[0])
			elif node.__mnemonic == self.Mnemonic.CALL:
				x, *r = args
				return x + '(' + ', '.join(r) +  ')'
			elif node.__mnemonic == self.Mnemonic.INDEX:
				x, y = args
				if node.__mnemonic in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					return x + '[' + y + ']'
				else:
					return '(' + x + ')[' + y + ']'
			elif node.__mnemonic == self.Mnemonic.NEG:
				x, = args
				if node.__mnemonic in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.NEG, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					return '-' + x
				else:
					return '-(' + x + ')'
			elif node.__mnemonic == self.Mnemonic.ADD:
				x, y = args
				if node.__operands[0].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.ADD, self.Mnemonic.SUB, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.ADD, self.Mnemonic.SUB, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' + ' + y
			elif node.__mnemonic == self.Mnemonic.SUB:
				x, y = args
				if node.__operands[0].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.ADD, self.Mnemonic.SUB, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.ADD, self.Mnemonic.SUB, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' - ' + y
			elif node.__mnemonic == self.Mnemonic.MUL:
				x, y = args
				if node.__operands[0].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' * ' + y
			elif node.__mnemonic == self.Mnemonic.FLOORDIV:
				x, y = args
				if node.__operands[0].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.MUL, self.Mnemonic.FLOORDIV, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' // ' + y
			elif node.__mnemonic == self.Mnemonic.POW:
				x, y = args
				if node.__operands[0].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.NEG, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' ** ' + y
			elif node.__mnemonic == self.Mnemonic.SHL:
				x, y = args
				if node.__operands[0].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.NEG, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' << ' + y
			elif node.__mnemonic == self.Mnemonic.XOR:
				x, y = args
				return x ^ y
			elif node.__mnemonic == self.Mnemonic.MOD:
				x, y = args
				if node.__operands[0].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic not in [self.Mnemonic.CONST, self.Mnemonic.ARG, self.Mnemonic.FOR, self.Mnemonic.NEG, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' % ' + y
			elif node.__mnemonic == self.Mnemonic.GT:
				x, y = args
				if node.__operands[0].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' > ' + y
			elif node.__mnemonic == self.Mnemonic.GE:
				x, y = args
				if node.__operands[0].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' >= ' + y
			elif node.__mnemonic == self.Mnemonic.LT:
				x, y = args
				if node.__operands[0].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' < ' + y
			elif node.__mnemonic == self.Mnemonic.LE:
				x, y = args
				if node.__operands[0].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' <= ' + y
			elif node.__mnemonic == self.Mnemonic.EQ:
				x, y = args
				if node.__operands[0].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' == ' + y
			elif node.__mnemonic == self.Mnemonic.NE:
				x, y = args
				if node.__operands[0].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					x = '(' + x + ')'
				if node.__operands[1].__mnemonic in [self.Mnemonic.GT, self.Mnemonic.LT, self.Mnemonic.GE, self.Mnemonic.LE, self.Mnemonic.EQ, self.Mnemonic.NE, self.Mnemonic.CALL, self.Mnemonic.INDEX]:
					y = '(' + y + ')'
				return x + ' != ' + y

			else:
				raise NotImplementedError
		
		return self.__traverse(action)
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + self.__mnemonic.name + ', ' + ', '.join([repr(_op) for _op in self.__operands]) + ')'
	
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
	
	def __and__(self, other):
		return self.__class__(self.Mnemonic.AND, self, self.__class__(other))
	
	def __mod__(self, other):
		return self.__class__(self.Mnemonic.MOD, self, self.__class__(other))
	
	def __getitem__(self, other):
		return self.__class__(self.Mnemonic.INDEX, self, self.__class__(other))
	
	def __call__(self, *args):
		return self.__class__(self.Mnemonic.CALL, self, *[self.__class__(_arg) for _arg in args])
	
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
	
	def __int__(self):
		try:
			value = self.evaluate()
		except NonConstantExpression:
			pass
		else:
			if not isinstance(value, self.__class__):
				return int(value)
		
		raise TypeError
	
	membership_test = False
	
	def __bool__(self):
		try:
			value = self.evaluate()
		except NonConstantExpression:
			value = self.simplify()
		else:
			if not isinstance(value, self.__class__):
				return bool(value)
		
		if self.__class__.membership_test or not hasattr(self.__class__, 'conditions'):
			if self.__mnemonic == self.Mnemonic.EQ:
				return self.__tree_equals(*self.__operands)
			elif self.__mnemonic == self.Mnemonic.NE:
				return not self.__tree_equals(*self.__operands)
			else:
				raise RuntimeError
		
		try:
			self.__class__.membership_test = True
			return self.__class__.conditions[value]
		except KeyError:
			raise MissingCondition(value)
		finally:
			self.__class__.membership_test = False
	
	@classmethod
	def merge_trees(cls, call, condition, yes_result, no_result):
		if yes_result.__mnemonic != no_result.__mnemonic:
			return call(condition, yes_result, no_result)
		elif yes_result.__mnemonic in [cls.Mnemonic.CONST, cls.Mnemonic.ARG, cls.Mnemonic.FOR]:
			if yes_result.__operands[0] == no_result.__operands[0]:
				return yes_result
			else:
				return call(condition, yes_result, no_result)
		elif yes_result.__mnemonic == cls.Mnemonic.IF:
			cond1, a1, b1 = yes_result.__operands
			cond2, a2, b2 = no_result.__operands
			if not cls.__tree_equals(cond1, cond2):
				return call(condition, yes_result, no_result)
			else:
				return cls(cls.Mnemonic.IF, cond1, cls.merge_trees(call, condition, a1, a2), cls.merge_trees(call, condition, b1, b2))
		elif yes_result.__mnemonic == cls.Mnemonic.LOOP:
			fors1, result1, init1, count1 = yes_result.__operands
			fors2, result2, init2, count2 = no_result.__operands
			if not cls.__tree_equals(fors1, fors2):
				return call(condition, yes_result, no_result)
			else:
				return cls(cls.Mnemonic.LOOP, fors1, cls.merge_trees(call, condition, result1, result2), cls.merge_trees(call, condition, init1, init2), cls.merge_trees(call, condition, count1, count2))
		else:
			return cls(yes_result.__mnemonic, *[cls.merge_trees(call, condition, _yes, _no) for (_yes, _no) in zip(yes_result.__operands, no_result.__operands)])


class Transformer(ast.NodeTransformer):
	def visit_Constant(self, orig_node):
		new_node = ast.parse(f'SymbolicValue({ast.unparse(orig_node)})')
		return new_node.body[0].value
  

def sm_range(limit):
	frame = inspect.stack()[1].frame
	orig_locals = dict(frame.f_locals)
	
	keys = list(sorted(orig_locals.keys()))
	
	for_vars = []
	n = 0
	while n < len(keys) + 1:
		for_vars.append(SymbolicValue.make_for(SymbolicValue.for_no))
		SymbolicValue.for_no += 1
		n += 1
	
	subst_locals = {}
	n = 0
	while n < len(keys):
		subst_locals[keys[n]] = for_vars[n + 1]
		n += 1
	
	frame.f_locals.update(subst_locals)
	pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0))
	
	yield for_vars[0]
	
	frame = inspect.stack()[1].frame
	new_locals = dict(frame.f_locals)
		
	loop_vars = frozenset(new_locals.keys()) - frozenset(orig_locals.keys())
	dynamic_vars = (frozenset(orig_locals.keys()) | frozenset(new_locals.keys())) - loop_vars
	
	init_values = [SymbolicValue(0)] + [orig_locals[_key] for _key in keys if _key in dynamic_vars]
	arg_values = [for_vars[0]] + [subst_locals[_key] for _key in keys if _key in dynamic_vars]
	
	result_values = [for_vars[0] + 1] + [new_locals[_key] for _key in keys if _key in dynamic_vars]
	
	loop = SymbolicValue.make_loop(arg_values, result_values, init_values, limit)
	iteration_values = dict(zip([_key for _key in keys if _key in dynamic_vars], [loop[_n] for _n in range(len(dynamic_vars) + 1)][1:]))
	
	frame.f_locals.update(iteration_values)
	pythonapi.PyFrame_LocalsToFast(py_object(frame), c_int(0))


def transform(fn):	
	source = 'if True:\n' + inspect.getsource(fn)
	orig_tree = ast.parse(source)
	mod_tree = Transformer().visit(orig_tree)
	code = compile(mod_tree, '<string>', 'exec')
	globals_ = {'range':sm_range, 'SymbolicValue':SymbolicValue}
	locals_ = {}
	exec(code, globals_, locals_)
	ft = locals_[fn.__name__]
	arg_len = len(inspect.getfullargspec(fn).args)
	args = [SymbolicValue.make_arg(_n) for _n in range(arg_len)]
	
	def run():
		try:
			for_no = SymbolicValue.for_no
			return ft(*args)
		
		except MissingCondition as error:
			condition = error.args[0]
			
			conditions = dict(SymbolicValue.conditions)
			
			SymbolicValue.conditions[condition] = True
			SymbolicValue.for_no = for_no
			yes_result = run()
			SymbolicValue.conditions = dict(conditions)
			
			SymbolicValue.conditions[condition] = False
			SymbolicValue.for_no = for_no
			no_result = run()
			SymbolicValue.conditions = dict(conditions)
			
			return SymbolicValue.merge_trees(SymbolicValue.make_if, condition, yes_result, no_result)
		
		except AssertionError:
			pass
		
		except (ArithmeticError, IndexError) as error:
			return SymbolicValue(0) # TODO
	
	SymbolicValue.for_no = 0
	SymbolicValue.conditions = {}

	circuit = run()
	
	del SymbolicValue.for_no
	del SymbolicValue.conditions
	
	circuit = circuit.optimize_loops()
	
	#print(fn.__name__, ":", circuit)
	
	short_t = IntType(8)
	long_t = IntType(16)
	lfn = Function(module, FunctionType(short_t, [short_t] * arg_len), fn.__name__)
	circuit.compile(lfn, long_t, {})
	
	def new_fn(*args):
		if len(args) != arg_len:
			raise TypeError
		
		k = [SymbolicValue.make_arg(_n) for _n in range(arg_len)]
		v = [SymbolicValue(_arg) for _arg in args]
		
		return circuit.substitute(k, v).evaluate()
	
	new_fn.__name__ = fn.__name__
	new_fn.__qualname__ = fn.__qualname__
	
	return new_fn


if __name__ == '__main__':
	from random import randrange
	from pathlib import Path
	from itertools import product
	from subprocess import Popen
	
	
	def fn_const():
		return 7


	def fn_ignore(x):
		return 8


	def fn_identity(x):
		return x


	def fn_project(x, y):
		return y


	def fn_inc(x):
		return x + 1
	
	
	def fn_add(x, y):
		return x + y
	
	
	def fn_cond(x, y):
		if x > y:
			return x
		else:
			return y
	
	
	def fn_conds(x, y):
		if x > y:
			if x > 3:
				return 1
		else:
			if y > 4:
				return 2
		
		if x < y:
			return 3
		
		return 4
	
	
	def fn_loop(x):
		r = 2
		a = x
		for i in range(x + 4):
			a -= i * r
			r += i * x
		return r // a
	
	
	def fn_inner_loop(x):
		q = 0
		r = 1
		for i in range(3):
			q += 1
			for j in range(6):
				r += i * x
				q += j
		return (q - r) & 0x7f
	
	
	def fn_simple_loop(x):
		r = 0
		for j in range(3):
			r += x
		return r
	
	
	def fn_2var_loop(x):
		a = 0 + x
		b = 1
		c = 2
		for j in range(a):
			b += x
			c -= j
		return a + b + c
	
	
	def fn_2cond_loop(x):
		a = 0 + x
		b = 1
		c = 2
		if b > x:
			for i in range(b):
				b += i
				c -= a
		for j in range(a):
			b += x
			c -= j
		return a + b + c
	
	
	def fn_double_loop(x):
		r = 0
		for i in range(3):
			r += i
		
		q = 0
		for j in range(3):
			q += j
			r += j
		
		return q - r
	
	
	def fn_cond_loop(x):
		r = 0
		for j in range(4):
			if j <= 2:
				r += x
			else:
				r -= x * (j + 1)
		return r
	
	
	def fn_ifn_for(x):
		r = 0
		if x > 1:
			for j in range(x):
				r += j
		return r
	
	
	def fn_for_if(x):
		r = 0
		for j in range(x):
			if j > 2:
				r += j
		return r
	
	
	def fn_loop_opt(x, y):
		q = 1
		r = 2
		
		for j in range(y):
			for i in range(x):
				r += j
		
		return (r // q) & 0x7f
	
	
	def fn_multi(x, y):
		q = 0
		
		if x > 0:
			for i in range(2):
				q += 1
		
		for j in range(3):
			q += 1
		
		return q
	
	
	module = Module()
	
	values_a = Path('a.values.txt').open('w')
	values_b = Path('b.values.txt').open('w')
	
	for fn in [fn_const, fn_ignore, fn_identity, fn_project, fn_inc, fn_add, fn_cond, fn_conds, fn_loop, fn_simple_loop, fn_double_loop, fn_inner_loop, fn_cond_loop, fn_ifn_for, fn_for_if, fn_loop_opt, fn_multi]:
		ft = transform(fn)
		arg_len = len(inspect.getfullargspec(fn).args)
		
		for n in range(10):
			r = [randrange(-20, 20) for _r in range(arg_len)]
			a = fn(*r)
			b = ft(*r)
			#print(ft.__name__, r, a, b)
			assert not isinstance(a, SymbolicValue)
			assert not isinstance(b, SymbolicValue)
			assert a == b, f"{ft.__name__}({', '.join([str(_r) for _r in r])}): {a} = {b}"
		
		values_a.write(fn.__name__)
		for r in product(*[range(-10, 10) for _r in range(arg_len)]):
			f = fn(*r)
			values_a.write("\t")
			values_a.write(",".join([str(_r) for _r in r]))
			values_a.write(":")
			values_a.write(str(f))
		values_a.write("\n")
		
		values_b.write(ft.__name__)
		for r in product(*[range(-10, 10) for _r in range(arg_len)]):
			f = ft(*r)
			values_b.write("\t")
			values_b.write(",".join([str(_r) for _r in r]))
			values_b.write(":")
			values_b.write(str(f))
		values_b.write("\n")
	
	values_a.close()
	values_b.close()
	
	Path('test.ll').write_text(str(module), 'utf-8')
	Popen('clang -o test.exe main.c test.ll -Wno-override-module -O3', shell=True).wait()
	Popen('./test.exe >c.values.txt', shell=True).wait()
	Popen('sha256sum a.values.txt b.values.txt c.values.txt', shell=True).wait()









