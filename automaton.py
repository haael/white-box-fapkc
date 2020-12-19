#!/usr/bin/python3
#-*- coding:utf8 -*-


from collections import deque
from itertools import product

from utils import memoize, parallel
from rings import *
from polynomial import *
from linear import *


__all__ = 'automaton_factory',


def automaton_factory(base_ring):
	"Returns an `Automaton` class using the specified `base_ring` for calculations."
	
	base_polynomial = Polynomial.get_algebra(base_ring=base_ring)
	base_vector = Vector.get_algebra(base_ring=base_polynomial)
	base_const_vector = Vector.get_algebra(base_ring=base_ring)
	base_matrix = Matrix.get_algebra(base_ring=base_polynomial)
	base_const_matrix = Matrix.get_algebra(base_ring=base_ring)
	
	class Automaton:
		"Finite automaton."
		
		class CacheDict:
			def __init__(self, creator, verifier):
				self.backstore = dict()
				self.creator = creator
				self.verifier = verifier
			
			def __getitem__(self, k):
				if not self.verifier(k):
					raise KeyError(f"Variable index {k} outside of allowed range.")
				
				try:
					return self.backstore[k]
				except KeyError:
					self.backstore[k] = self.creator(k)
					return self.backstore[k]
			
			def keys(self):
				return self.backstore.keys()
		
		x = CacheDict((lambda k: base_polynomial.var(f'x_{k}')), (lambda k: k >= 0))
		s = CacheDict((lambda k: base_polynomial.var(f's_{k[0]}_{k[1]}')), (lambda k: k[0] >= 1 and k[1] >= 0))
		
		def __init__(self, output_transition=None, state_transition=None):
			"""
			`output_transition` - vector of polynomials producing the output symbol vector
			`state_transition` - vector of polynomials producing the next state vector to be appended to the history queue
			"""
			
			if output_transition == None: output_transition = base_vector.zero(0)
			if state_transition == None: state_transition = base_vector.zero(0)
			
			self.output_transition = output_transition
			self.state_transition = state_transition
		
		def transition(self, x, history):
			"""
			Takes the input symbol `x` (vector over a ring)
			and the automaton state (`history`) collection (preferably queue) of vectors.
			Inserts the new state vector at position 0 in `history` and deletes the tail
			if `history` is longer than memory order.
			Returns the output symbol. The automaton state (`history`) is modified in place.
			"""
			
			state = {}
			for t, sh in enumerate(history):
				for i, si in enumerate(sh):
					state[str(self.s[t + 1, i])] = si
			for i, xi in enumerate(x):
				state[str(self.x[i])] = xi
			
			y = self.output_transition(**state).evaluate()
			s = self.state_transition(**state).evaluate()
			
			history.insert(0, s)
			while len(history) > self.memory_length:
				history.pop()
			return y
		
		def __call__(self, in_stream):
			"Takes the stream of input symbols, yields the stream of output symbols. Starts from the state composed of zero vectors."
			history = deque([base_vector.zero(self.memory_width)] * self.memory_length) # initial state
			for x in in_stream:
				yield self.transition(x, history)
		
		def __matmul__(self, other):
			"Automaton composition."
			
			shift = other.memory_width
			
			substitution = {}
			for i, yi in enumerate(other.output_transition):
				substitution[str(self.x[i])] = yi
			for t in range(1, self.memory_length + 1):
				for i in range(self.memory_width):
					substitution[str(self.s[t, i])] = self.s[t, i + shift]
			
			output_transition = base_vector(_trans(**substitution) for _trans in self.output_transition)
			state_transition = base_vector(chain(other.state_transition, (_trans(**substitution) for _trans in self.state_transition)))
			
			return self.__class__(output_transition, state_transition)
		
		@property
		def input_size(self):
			v = frozenset().union(*[_c.variables() for _c in self.state_transition.values()]) | frozenset().union(*[_c.variables() for _c in self.output_transition.values()])
			if not v:
				return 0
			m = 0
			for var in v:
				for k in self.x.keys():
					if self.x[k] == var:
						m = max(m, k)
			return m
		
		@property
		def output_size(self):
			return self.output_transition.dimension
		
		@property
		@memoize
		def memory_length(self):
			v = frozenset().union(*[_c.variables() for _c in self.state_transition.values()]) | frozenset().union(*[_c.variables() for _c in self.output_transition.values()])
			if not v:
				return 0
			m = 0
			for var in v:
				for k in self.s.keys():
					if self.s[k] == var:
						a, b = k
						m = max(m, a)
			return m
		
		@property
		@memoize
		def memory_width(self):
			return self.state_transition.dimension
		
		def optimize(self):
			self.output_transition = self.output_transition.optimized()
			self.state_transition = self.state_transition.optimized()
		
		def mix_states(self):
			mix, unmix = base_const_matrix.random_inverse_pair(self.memory_width)
			mix = base_matrix(mix)
			unmix = base_matrix(unmix)
			
			substitution = {}
			for t in range(1, self.memory_length + 1):
				unmixed = unmix @ base_vector(self.s[t, _i] for _i in range(self.memory_width))
				for i in range(self.memory_width):
					substitution[str(self.s[t, i])] = unmixed[i]
			
			self.state_transition = mix @ base_vector(_trans(**substitution) for _trans in self.state_transition)
			self.output_transition = base_vector(_trans(**substitution) for _trans in self.output_transition)
		
		def __and__(self, other):
			"2 automata running in parallel (aka tuple). The input size is the sum of input sized of the provided automata. The output size is the sum of the sizes of outputs."
			raise NotImplementedError
		
		def __or__(self, other):
			"Choice of 1 automaton from 2 running in parallel (aka tagged union). Input sizes of the provided automata must be equal, output likewise. The input sie of the resulting automaton will be 1 position longer. The 1st argument decides which automaton returns the output."
			raise NotImplementedError
		
		def cast(cls, begin, end):
			"Narrow the output to the range given."
			raise NotImplementedError
		
		@classmethod
		def countdown(cls, block_size, memory_size, offset, length, period): # TODO
			x = base_vector(cls.x[_i] for _i in range(block_size))
			s = base_vector(cls.s[1, _i] for _i in range(block_size))
			
			set_point = base_vector(period, dimension=block_size)
			
			in_switch = base_ring.zero()
			for i in range(block_size):
				in_switch |= s[i] - set_point[i]
			
			def full_adder(a, b, c):
				return a + b + c, a * b | b * c | c * a
			
			bsum = []
			c = base_ring.zero()
			for i in range(block_size):
				r, c = full_adder(s[i], (in_switch if i == 0 else base_ring.zero()), c)
				bsum.append(r)
			state_transition = base_vector(bsum)
			
			out_switch = base_ring.zero()
			for i in range(block_size):
				out_switch |= s[i] - set_point[i]
			output_transition = x * out_switch
			
			return cls(output_transition=output_transition, state_transition=state_transition)
		
		@classmethod
		def repeater(cls, block_size, delay=0):
			"A simple automaton that returns back its input with optional delay."
			
			if delay == 0:
				state_transition = base_vector.zero(block_size)
				output_transition = base_vector(cls.x[_i] for _i in range(width))
			else:
				state_transition = base_vector(cls.x[_i] for _i in range(width))
				output_transition = base_vector(cls.s[delay, _i] for _i in range(width))
			
			return cls(output_transition=output_transition, state_transition=state_transition)
		
		def passthrough(self, offset, length, period):
			return (self.repeater(self.block_size) | self) @ (self.countdown(self.block_size, self.memory_size, offset, length, period) & self.repeater(self.block_size))
		
		@classmethod
		def linear_nodelay_wifa_pair(cls, block_size=8, memory_size=32):
			"Returns a pair of linear finite automata with 0 delay, being their respective inverses."
			
			x = base_vector(cls.x[_i] for _i in range(block_size))
			s = [None]
			for n in range(1, memory_size + 1):
				s.append(base_vector(cls.s[n, _i] for _i in range(block_size)))
			
			ms, mi = base_const_matrix.random_inverse_pair(block_size)
			ms = base_matrix(ms)
			mi = base_matrix(mi)
			
			ya = ms @ x
			yb = mi @ x
			for n in range(1, memory_size + 1):
				m = base_matrix(base_const_matrix.random(block_size, block_size))
				ya += m @ s[n]
				yb -= mi @ m @ s[n]
			
			automaton_A = cls(output_transition=ya, state_transition=x)
			automaton_B = cls(output_transition=yb, state_transition=yb)
			return automaton_A, automaton_B
		
		@classmethod
		def linear_delay_wifa_pair(cls, block_size=8, memory_size=32):
			"Generate a linear FA with the delay specified by `memory_size`."
			
			class BadLuck(BaseException):
				"Exception that is thrown when the random objects do not have desired properties and need to be generated again."
				pass
			
			while True: # repeat until successful
				try:
					coefficients_A = []
					for n in range(memory_size + 1):
						coefficients_A.append(base_matrix.random_rank(block_size, block_size - 1))
					
					x = [base_vector(cls.x[_i] for _i in range(block_size))]
					for n in range(1, memory_size + 1):
						x.append(base_vector(cls.s[n, _i] for _i in range(block_size)))
					
					y = base_vector.zero(block_size)
					for n in range(memory_size + 1):
						y += coefficients_A[n] @ x[n]
					
					automaton_A = cls(output_transition=y.optimized(), state_transition=x[0])
					
					del x, y
					
					# `P` matrix calculation
					zero_v = base_vector.zero(block_size)
					unit_m = base_matrix.unit(block_size)
					zero_m = base_matrix.zero(block_size, block_size)
					
					matrix_A = dict()
					for i in range(memory_size + 1):
						for j in range(i + 1):
							matrix_A[i, j] = coefficients_A[i - j][...]
					
					if __debug__:
						original_A = dict((_k, _v[...]) for (_k, _v) in matrix_A.items())
						
						def compare_coefficients():
							for p in range(memory_size + 1):
								for q in range(memory_size + 1):
									c_A = zero_m[...]
									for k in range(memory_size + 1):
										try:
											c_A += matrix_P[p, k] @ original_A[k, q]
										except KeyError:
											pass
									
									try:
										assert c_A == matrix_A[p, q]
									except KeyError:
										assert c_A == zero_m
					
					matrix_P = dict()
					for i in range(memory_size + 1):
						for j in range(memory_size + 1):
							if i != j:
								matrix_P[i, j] = zero_m[...]
							elif i == j:
								matrix_P[i, j] = unit_m[...]
					
					#if __debug__:
					#	i = -1
					#	compare_coefficients()
					
					for i in reversed(range(memory_size + 1)):
						mm = []
						for p in range(i + 1):
							for q in range(p + 1):
								mm.append(matrix_A[p, q])
						
						pu = unit_m[...]
						mm.append(pu)
						
						matrix_A[i, i].echelon(*mm)
						
						del mm
						
						for p in range(i + 1):
							for q in range(memory_size + 1):
								matrix_P[p, q] = pu @ matrix_P[p, q]
						
						#if __debug__:
						#	compare_coefficients()
						
						for j in range(block_size):
							if matrix_A[0, 0][j, :] == zero_v:
								ll = j
								break
						else:
							ll = block_size
							#continue
						
						psI_m = base_matrix.diagonal([base_ring.one() if _j <  ll else base_ring.zero() for _j in range(block_size)])
						psO_m = base_matrix.diagonal([base_ring.one() if _j >= ll else base_ring.zero() for _j in range(block_size)])
						
						matrix_Ps = dict()
						
						for p in range(i):
							for q in range(p + 1):
								for j in range(ll, block_size):
									matrix_A[p, q][j, :] = matrix_A[p + 1, q][j, :]
							for q in range(memory_size + 1):
								matrix_Ps[p, q] = psI_m @ matrix_P[p, q] + psO_m @ matrix_P[p + 1, q]
						
						for q in range(i + 1):
							for j in range(ll, block_size):
								matrix_A[i, q][j, :] = zero_v
						for q in range(memory_size + 1):
							matrix_Ps[i, q] = psI_m @ matrix_P[i, q] + psO_m @ matrix_P[0, q]
						
						for k, v in matrix_Ps.items():
							matrix_P[k] = v
						
						del matrix_Ps
						
						#if __debug__:
						#	compare_coefficients()
					
					if __debug__:
						i = -1
						compare_coefficients()
					
					A00 = matrix_A[0, 0]
					
					for j in range(block_size):
						if A00[j, :] == zero_v:
							raise BadLuck("Leading matrix not invertible, try again.")
					
					A00_inv = A00.inverse()
					
					del A00, matrix_A
					
					coefficients_P = [(A00_inv @ matrix_P[0, _j]).optimized() for _j in range(memory_size + 1)]
					
					coefficients_Q = [zero_m]
					for q in range(1, memory_size + 1):
						r = zero_m[...]
						for k in range(memory_size + 1):
							r += matrix_P[0, k] @ (coefficients_A[k + q][...] if (k + q < memory_size) else zero_m[...]) # FIXME: correct?
						coefficients_Q.append((A00_inv @ r).optimized())
					
					x = [base_vector.zero(block_size)]
					y = [base_vector(cls.x[_i] for _i in range(block_size))]
					
					for n in range(1, memory_size + 1):
						x.append(base_vector(cls.s[n, _i] for _i in range(block_size)))
						y.append(base_vector(cls.s[n, _i + block_size] for _i in range(block_size)))
					
					x0 = zero_v[:]
					for n in range(memory_size + 1):
						x0 += coefficients_Q[n] @ x[n]
						x0 += coefficients_P[n] @ y[-n]
					x[0] = x0.optimized()
					
					automaton_B = cls(output_transition=x[0], state_transition=base_vector(list(x[0]) + list(y[0])))
					
					raise NotImplementedError
					
					return automaton_A, automaton_B
				except BadLuck:
					# TODO: reset entropy
					pass
		
		@classmethod
		def nonlinear_nodelay_wifa_pair(cls, block_size=8, memory_size=32):
			raise NotImplementedError
		
		@classmethod
		def fapkc0(cls, block_size=8, memory_size=32):
			"Generate (public, private) pair of random FAPKC0 keys. WARNING: FAPKC0 is broken; do not use in production."
			
			ls, li = cls.linear_delay_wifa_pair(block_size=block_size, memory_size=memory_size)
			ns, ni = cls.nonlinear_nodelay_wifa_pair(block_size=block_size, memory_size=memory_size)
			return ns @ ls, li @ ni
		
		def compile(self, name, module):
			self.state_transition.compile(name + '_st', module)
			self.output_transition.compile(name + '_ot', module)
		
		def wrap_compiled(self, name, engine):
			st = self.state_transition.wrap_compiled(name + '_st', engine)
			ot = self.output_transition.wrap_compiled(name + '_ot', engine)
			
			def t(x, history):
				state = {}
				for t, sh in enumerate(history):
					for i, si in enumerate(sh):
						state[str(self.s[t + 1, i])] = si
				for i, xi in enumerate(x):
					state[str(self.x[i])] = xi
				
				y = ot(**state)
				s = st(**state)
				
				history.insert(0, s)
				while len(history) > self.memory_length:
					history.pop()
				return y
			
			def fn(in_stream):
				history = deque([base_vector.zero(self.memory_width)] * self.memory_length)
				for x in in_stream:
					yield t(x, history)
			
			return fn	
	
	
	Automaton.base_ring = base_ring
	Automaton.base_const_vector = base_const_vector
	Automaton.base_const_matrix = base_const_matrix
	Automaton.base_polynomial = base_polynomial
	Automaton.base_vector = base_vector
	Automaton.base_matrix = base_matrix
	
	return Automaton


if __debug__:
	import pickle
	from itertools import chain, tee
	
	def test_automaton_composition(Ring, block_size, memblock_size, length):
		print("Automaton composition test")
		print(" algebra:", Ring, ", data block size:", block_size, ", memory block size:", memblock_size, ", stream length:", length)
		
		Automaton = automaton_factory(Ring)
		Vector = Automaton.base_vector
		ConstVector = Automaton.base_const_vector
		
		x = Vector([Automaton.x[_i] for _i in range(block_size)])
		s_1 = Vector([Automaton.s[1, _i] for _i in range(memblock_size)])
		s_2 = Vector([Automaton.s[2, _i] for _i in range(memblock_size)])
		s_3 = Vector([Automaton.s[3, _i] for _i in range(memblock_size)])
		
		variables = list(x) + list(s_1) + list(s_2) + list(s_3)
		
		def automaton_input():
			for i in range(length):
				yield ConstVector.random(block_size)
		
		for i in range(5):
			print(" round", i)
			automaton1 = Automaton(Vector.random(dimension=block_size, variables=variables, order=i), Vector.random(dimension=memblock_size, variables=variables, order=i))
			automaton2 = Automaton(Vector.random(dimension=block_size, variables=variables, order=i), Vector.random(dimension=memblock_size, variables=variables, order=i))
			automaton3 = automaton1 @ automaton2
			
			print("  optimizing automata...")
			automaton1.optimize()
			automaton2.optimize()
			automaton3.optimize()
			
			print("  encryption test...")
			input1, input2 = tee(automaton_input())
			for n, (a, b) in enumerate(zip(automaton3(input1), automaton1(automaton2(input2)))):
				print(n, a, b)
				assert a == b
	
	def test_automaton_compilation(Ring, block_size, memblock_size, length):
		print("Automaton compilation test")
		print(" algebra:", Ring, ", data block size:", block_size, ", memory block size:", memblock_size, ", stream length:", length)
		
		Automaton = automaton_factory(Ring)
		Vector = Automaton.base_vector
		ConstVector = Automaton.base_const_vector
		
		x = Vector([Automaton.x[_i] for _i in range(block_size)])
		s_1 = Vector([Automaton.s[1, _i] for _i in range(memblock_size)])
		s_2 = Vector([Automaton.s[2, _i] for _i in range(memblock_size)])
		s_3 = Vector([Automaton.s[3, _i] for _i in range(memblock_size)])
		
		variables = list(x) + list(s_1) + list(s_2) + list(s_3)
		
		def automaton_input():
			for i in range(length):
				yield ConstVector.random(block_size)
		
		for i in range(5):
			print(" round", i)
			automaton1 = Automaton(Vector.random(dimension=block_size, variables=variables, order=i), Vector.random(dimension=memblock_size, variables=variables, order=i))
			automaton2 = Automaton(Vector.random(dimension=block_size, variables=variables, order=i), Vector.random(dimension=memblock_size, variables=variables, order=i))
			automaton3 = automaton1 @ automaton2
			
			print("  optimizing automata...")
			automaton1.optimize()
			automaton2.optimize()
			automaton3.optimize()
			
			print("  compiling automata...")
			from jit_types import Module
			module = Module()
			automaton1.compile('a1', module)
			automaton2.compile('a2', module)
			automaton3.compile('a3', module)
			engine = module.compile()
			automaton1c = automaton1.wrap_compiled('a1', engine)
			automaton2c = automaton2.wrap_compiled('a2', engine)
			automaton3c = automaton3.wrap_compiled('a3', engine)
			
			print("  encryption test...")
			input1, input2 = tee(automaton_input())
			input1a, input1b = tee(input1)
			input2a, input2b = tee(input2)
			
			print("   python code...")
			out1 = []
			for n, (a, b) in enumerate(zip(automaton3(input1a), automaton1(automaton2(input2a)))):
				#print(n, a, b)
				assert a == b
				out1.append(a)
			
			print("   native code...")
			out2 = []
			for n, (a, b) in enumerate(zip(automaton3c(input1b), automaton1c(automaton2c(input2b)))):
				#print(n, a, b)
				assert a == b
				out2.append(a)
			
			assert out1 == out2

	
	def test_state_mixing(Ring, block_size, memblock_size, length):
		print("State mixing test")
		print(" algebra:", Ring, ", data block size:", block_size, ", memory block size:", memblock_size, ", stream length:", length)
		
		Automaton = automaton_factory(Ring)
		Vector = Automaton.base_vector
		ConstVector = Automaton.base_const_vector
		
		x = Vector([Automaton.x[_i] for _i in range(block_size)])
		s_1 = Vector([Automaton.s[1, _i] for _i in range(memblock_size)])
		s_2 = Vector([Automaton.s[2, _i] for _i in range(memblock_size)])
		s_3 = Vector([Automaton.s[3, _i] for _i in range(memblock_size)])
		
		variables = list(x) + list(s_1) + list(s_2) + list(s_3)
		
		def automaton_input():
			for i in range(length):
				yield ConstVector.random(block_size)
		
		for i in range(5):
			print(" round", i)
			automaton1 = Automaton(Vector.random(dimension=block_size, variables=variables, order=i), Vector.random(dimension=memblock_size, variables=variables, order=i))
			automaton2 = Automaton(state_transition=Vector(automaton1.state_transition), output_transition=Vector(automaton1.output_transition))
			automaton2.mix_states()
			
			automaton1.optimize()
			automaton2.optimize()
			
			#print(automaton1.output_transition)
			#print(automaton1.state_transition)
			#print(automaton2.output_transition)
			#print(automaton2.state_transition)
			
			input1, input2 = tee(automaton_input())
			for a, b in zip(automaton1(input1), automaton2(input2)):
				assert a == b
	
	def test_fapkc_encryption(Ring, block_size, memblock_size, length):
		print("FAPKC encryption / decryption test")
		print(" algebra:", Ring, ", data block size:", block_size, ", memory block size:", memblock_size, ", stream length:", length)
		
		Automaton = automaton_factory(Ring)
		ConstVector = Automaton.base_const_vector
		
		def automaton_input():
			for i in range(length):
				yield ConstVector.random(block_size)
		
		for i in range(5):
			print(" round", i)
			mixer, unmixer = Automaton.linear_nodelay_wifa_pair(block_size=block_size, memory_size=i)
			
			input1, input2 = tee(automaton_input())
			for a, b in zip(input1, unmixer(mixer(input2))):
				assert a == b
	
	def test_homomorphic_encryption(Ring, block_size, memblock_size, length):
		print("Gonzalez-Llamas homomorphic encryption test")
		print(" algebra:", Ring, ", data block size:", block_size, ", memory block size:", memblock_size, ", stream length:", length)
		
		Automaton = automaton_factory(Ring)
		Vector = Automaton.base_vector
		ConstVector = Automaton.base_const_vector
		
		x = Vector([Automaton.x[_i] for _i in range(block_size)])
		s_1 = Vector([Automaton.s[1, _i] for _i in range(memblock_size)])
		s_2 = Vector([Automaton.s[2, _i] for _i in range(memblock_size)])
		s_3 = Vector([Automaton.s[3, _i] for _i in range(memblock_size)])
		
		variables = list(x) + list(s_1) + list(s_2) + list(s_3)
		
		def automaton_input():
			for i in range(length):
				yield ConstVector.random(block_size)
		
		for i in range(5):
			print(" round", i)
			print("  generating automata...")
			mixer, unmixer = Automaton.linear_nodelay_wifa_pair(block_size=block_size, memory_size=4)
			plain_automaton = Automaton(Vector.random(dimension=block_size, variables=variables, order=3), Vector.random(dimension=memblock_size, variables=variables, order=3))
			
			print("  composing automata...")
			homo_automaton = mixer @ plain_automaton @ unmixer
			homo_automaton.mix_states()
			
			print("  optimizing automata...")
			print(f"   mixer: {mixer.output_transition.circuit_size()} {mixer.state_transition.circuit_size()} {mixer.output_transition.dimension} {mixer.state_transition.dimension}")
			mixer.optimize()
			print(f"          {mixer.output_transition.circuit_size()} {mixer.state_transition.circuit_size()}")
			print(f"   unmixer: {unmixer.output_transition.circuit_size()} {unmixer.state_transition.circuit_size()} {unmixer.output_transition.dimension} {unmixer.state_transition.dimension}")
			unmixer.optimize()
			print(f"            {unmixer.output_transition.circuit_size()} {unmixer.state_transition.circuit_size()}")
			print(f"   plain: {plain_automaton.output_transition.circuit_size()} {plain_automaton.state_transition.circuit_size()} {plain_automaton.output_transition.dimension} {plain_automaton.state_transition.dimension}")
			plain_automaton.optimize()
			print(f"          {plain_automaton.output_transition.circuit_size()} {plain_automaton.state_transition.circuit_size()}")
			print(f"   homomorphic: {homo_automaton.output_transition.circuit_size()} {homo_automaton.state_transition.circuit_size()} {homo_automaton.output_transition.dimension} {homo_automaton.state_transition.dimension}")
			homo_automaton.optimize()
			print(f"                {homo_automaton.output_transition.circuit_size()} {homo_automaton.state_transition.circuit_size()}")

			print("  compiling automata...")
			from jit_types import Module
			module = Module()
			mixer.compile('m', module)
			unmixer.compile('u', module)
			plain_automaton.compile('p', module)
			homo_automaton.compile('h', module)
			engine = module.compile()
			mixer = mixer.wrap_compiled('m', engine)
			unmixer = unmixer.wrap_compiled('u', engine)
			plain_automaton = plain_automaton.wrap_compiled('p', engine)
			homo_automaton = homo_automaton.wrap_compiled('h', engine)
			
			print("  encryption/decryption test...")
			input1, input2 = tee(automaton_input())
			for n, (a, b) in enumerate(zip(plain_automaton(input1), unmixer(homo_automaton(mixer(input2))))):
				print(n, a, b)
				assert a == b
	
	def automaton_test_suite(verbose=False):
		if verbose: print("running test suite")
		
		Automaton = automaton_factory(BooleanRing.get_algebra())
		Vector = Automaton.base_vector
		
		ls, li = Automaton.linear_delay_wifa_pair(block_size=8, memory_size=3)
		
		zero_pad = [Vector.zero(8) for _i in range(3)]
		i_seq = [Vector.random(8) for _i in range(20)]
		i_pad = [Vector.random(8) for _i in range(3)]
		o_seq = list(ls(i_seq + i_pad))
		d_seq = list(li(o_seq + zero_pad))
		
		print([hex(int(_x))[2:] for _x in i_seq + i_pad])
		print([hex(int(_x))[2:] for _x in o_seq + zero_pad])
		print([hex(int(_x))[2:] for _x in d_seq])
		
		print()
		history = [Vector.zero(8) for _i in range(3)]
		vi = Vector.random(8)
		vo = ls.transition(vi, history)
		print(hex(int(vi))[2:])
		print(hex(int(vo))[2:])
		print([hex(int(_v))[2:] for _v in history])
		vi = Vector.random(8)
		vo = ls.transition(vi, history)
		print(hex(int(vi))[2:])
		print(hex(int(vo))[2:])
		print([hex(int(_v))[2:] for _v in history])
		vi = Vector.random(8)
		vo = ls.transition(vi, history)
		print(hex(int(vi))[2:])
		print(hex(int(vo))[2:])
		print([hex(int(_v))[2:] for _v in history])
		
		quit()
		
		#Automaton.fapkc0(memory_size=6)
		
		'''
		for i in (2, 3, 4, 5, 16, 64, 128, 512, 1024):
			if verbose: print()
			if verbose: print("test ModularRing(size={})".format(i))
			ring = ModularRing.get_algebra(size=i)
			if verbose: print(" automaton test")
			test_automaton_composition(ring)
		'''
		
		if verbose: print()
		if verbose: print("test BooleanRing()")
		ring = BooleanRing.get_algebra()
		if verbose: print(" automaton test")
		test_automaton_composition(ring)
		
		'''
		for i in (2, 3, 4, 5, 16, 64, 128, 512, 1024):
			if verbose: print()
			if verbose: print("test GaloisRing(size={})".format(i))
			field = GaloisField.get_algebra(size=i)
			if verbose: print(" automaton test")
			test_automaton_composition(field)
		
		assert BinaryRing.get_algebra(exponent=1)(1) != RijndaelRing(1)
		
		for i in (2, 3, 4, 5, 8, 9, 10):
			if verbose: print()
			if verbose: print("test BinaryRing(exponent={})".format(i))
			field = BinaryRing.get_algebra(exponent=i)
			if verbose: print(" automaton test")
			test_automaton_composition(field)
		'''
		
		if verbose: print()
		if verbose: print("test RijndaelField()")
		field = RijndaelField
		if verbose: print(" automaton test")
		test_automaton_composition(field)
		
	__all__ = __all__ + ('test_automaton_composition', 'test_fapkc_encryption', 'test_homomorphic_encryption', 'automaton_test_suite',)


if __debug__ and __name__ == '__main__':
	#test_automaton_compilation(BooleanRing.get_algebra(), 8, 4, 256)
	#test_automaton_compilation(RijndaelField.get_algebra(), 4, 2, 64)

	with parallel():
	#	test_automaton_composition(BooleanRing.get_algebra(), 8, 4, 256)
	#	test_automaton_composition(RijndaelField.get_algebra(), 4, 2, 64)
	#
	#	test_state_mixing(BooleanRing.get_algebra(), 8, 4, 256)
	#	test_state_mixing(RijndaelField.get_algebra(), 4, 2, 64)
	#
	#	test_fapkc_encryption(BooleanRing.get_algebra(), 8, 4, 16)
	#	test_fapkc_encryption(RijndaelField.get_algebra(), 4, 2, 16)
	#
		test_homomorphic_encryption(BooleanRing.get_algebra(), 8, 4, 32)
		test_homomorphic_encryption(RijndaelField.get_algebra(), 4, 2, 8)
	
	#Automaton = automaton_factory(BooleanRing.get_algebra())
	#Vector = Automaton.base_vector
	
	#cd10a = Automaton.countdown_gadget(ticks=10, prefix=True)
	#cd10b = Automaton.countdown_gadget(ticks=10, prefix=False)
	
	#input_stream = [Vector(_n, dimension=8) for _n in range(20)]
	#print(list(int(_x) for _x in cd10a(input_stream)))
	#print(list(int(_x) for _x in cd10b(input_stream)))



