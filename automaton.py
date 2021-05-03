#!/usr/bin/python3 -O
#-*- coding:utf8 -*-


from collections import deque
from itertools import product, chain
from time import time
from pathlib import Path

from utils import memoize, parallel, randbelow
from rings import *
from polynomial import *
from linear import *
from jit_types import Compiler


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
			
			y = self.output_transition(**state)			
			try:
				y = y.evaluate()
			except ValueError:
				pass
			
			s = self.state_transition(**state)
			try:
				s = s.evaluate()
			except ValueError:
				pass
			
			history.insert(0, s)
			while len(history) > self.memory_length:
				history.pop()
			return y
		
		def __call__(self, in_stream, initial_state=None):
			"Takes the stream of input symbols, yields the stream of output symbols. Starts from the state composed of zero vectors."
			
			if initial_state == None:
				history = deque([base_const_vector.zero(self.memory_width)] * self.memory_length) # initial state
			else:
				history = deque(initial_state)
				if len(history) != self.memory_length:
					raise ValueError("Invalid initial state length")
				if any(_element.dimension != self.memory_width for _element in history):
					raise ValueError("Invalid vector width in initial state")
			
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
			v = frozenset(str(_v) for _v in frozenset().union(*[_c.variables() for _c in self.state_transition.values()]) | frozenset().union(*[_c.variables() for _c in self.output_transition.values()]))
			if not v:
				return 0
			
			m = 0
			for va in v:
				vs = str(va).split('_')
				if vs[0] != 's': continue # FIXME: assumes variable naming
				m = max(m, int(vs[1]))
			
			#m = 0
			#for i in range(1, 64): # FIXME: remove hard limits
			#	for j in range(256):
			#		if str(self.s[i, j]) in v:
			#			m = i
			
			return m
		
		@property
		@memoize
		def memory_width(self):
			#print("memory_width", self.state_transition.dimension)
			return self.state_transition.dimension
		
		def optimize(self):
			self.output_transition = self.output_transition.optimized()
			self.state_transition = self.state_transition.optimized()
		
		@staticmethod
		def random_nonlinear_equation_pair(length):
			print(" generating first set")
			b1 = base_vector(base_polynomial.var('a_' + str(_i)) for _i in range(length))
			b2 = base_vector((base_polynomial.var('a_' + str(_i - randbelow(_i) - 1)) * base_polynomial.var('a_' + str(_i - randbelow(_i) - 1))) if _i else base_polynomial.zero() for _i in range(length))
			b = b2 + b1
			b = b.optimized()
			
			print(" generating second set")
			a1 = base_vector(base_polynomial.var('b_' + str(_i)) for _i in range(length))
			subst = {}
			a = base_vector.zero(length)
			for i in range(length):
				a[i] = (-b2[i](**subst) + a1[i]).optimized()
				subst['a_' + str(i)] = a[i]
			
			#return a1, b1
			return a, b
		
		def mix_states(self):
			"""
			To factorize a compound automaton it is necessary and sufficient to split its state vector into the part related to the first automaton and the part related to the second automaton.
			The naive composition algorithm produces an automaton where the parts are simply concatenated, which leaves them open to factorization by the attacker. To prevent that, the state
			representation must be obfuscated.
			This function applies a linear transform to the state vector. In order to factorize the automaton into components, the attacker must guess the transformation matrix. In order to
			learn one bit of one of the original states, he must guess one row of the matrix. The transformation is a square matrix of the size equal to the number of bits of the compound state
			squared.
			This function is slow. While debugging, this step might be omitted.
			"""
			
			print("generating random permutation", self.memory_width)
			mix, unmix = base_const_matrix.random_permutation_pair(self.memory_width)
			mix = base_matrix(mix)
			unmix = base_matrix(unmix)
			
			print("generating random nonlinear transformation")
			mix_nonlinear, unmix_nonlinear = self.random_nonlinear_equation_pair(self.memory_width)
			print(" size:", mix_nonlinear.circuit_size(), unmix_nonlinear.circuit_size())
			
			print("calculating unmix substitution")
			print(" matrix step")
			unmixed = unmix @ base_vector(base_polynomial.var(f'c_{_i}') for _i in range(self.memory_width))
			#unmixed = base_vector(base_polynomial.var(f'c_{_i}') for _i in range(self.memory_width))
			print(" substitution step")
			unmixed = unmix_nonlinear(**{f'a_{_i}' : unmixed[_i] for _i in range(self.memory_width)})
			print(" before optimization:", unmixed.circuit_size(), [_c.circuit_size() for _c in unmixed])
			unmixed = unmixed.optimized()
			print(" after optimization:", unmixed.circuit_size(), [_c.circuit_size() for _c in unmixed])
			
			substitution = {}
			for t in range(1, self.memory_length + 1):
				for i in range(self.memory_width):
					substitution[str(self.s[t, i])] = unmixed[i](**{f'c_{_i}' : self.s[t, _i] for _i in range(self.memory_width)})
			
			print("applying state transition")
			print(" size:", self.state_transition.circuit_size())
			bvt = base_vector(_trans(**substitution) for _trans in self.state_transition)
			print(" step1", bvt.circuit_size(), [_c.circuit_size() for _c in bvt])
			bvt = bvt.optimized()
			print(" step2", bvt.circuit_size(), [_c.circuit_size() for _c in bvt])
			self.state_transition = mix @ mix_nonlinear(**{f'b_{_i}' : bvt[_i] for _i in range(self.memory_width)})
			#self.state_transition = mix_nonlinear(**{f'b_{_i}' : bvt[_i] for _i in range(self.memory_width)})
			print(" result:", self.state_transition.circuit_size())
			print("applying output transition")
			print(" size:", self.output_transition.circuit_size())
			self.output_transition = base_vector(_trans(**substitution) for _trans in self.output_transition)
			print(" result:", self.output_transition.circuit_size())
		
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
		
		#@classmethod
		#def repeater(cls, block_size, delay=0):
		#	"A simple automaton that returns back its input with optional delay."
		#	
		#	if delay == 0:
		#		state_transition = base_vector.zero(block_size)
		#		output_transition = base_vector(cls.x[_i] for _i in range(width))
		#	else:
		#		state_transition = base_vector(cls.x[_i] for _i in range(width))
		#		output_transition = base_vector(cls.s[delay, _i] for _i in range(width))
		#	
		#	return cls(output_transition=output_transition, state_transition=state_transition)
		#
		#def passthrough(self, offset, length, period):
		#	return (self.repeater(self.block_size) | self) @ (self.countdown(self.block_size, self.memory_size, offset, length, period) & self.repeater(self.block_size))
		
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
			"Generate a pair or linear FAs with the delay specified by `memory_size`. Algorithm described briefly in 'Break Finite Automata Public Key Cryptosystem' by Feng Bao and Yoshihide Igarashi."
			
			class BadLuck(BaseException):
				"Exception that is thrown when the random objects do not have desired properties and need to be generated again."
				pass
			
			zero_v = base_const_vector.zero(block_size)
			unit_m = base_const_matrix.unit(block_size)
			zero_m = base_const_matrix.zero(block_size, block_size)
			
			while True: # repeat until successful
				try:
					assert zero_v.is_zero()
					assert unit_m.is_one()
					assert zero_m.is_zero()
					
					#print(" linear_delay_wifa_pair", 1)
					coefficients_A = []
					for n in range(memory_size + 1):
						rank = min(block_size, max(block_size // 2 + 2, block_size + n - memory_size))
						m = base_const_matrix.random_rank(block_size, rank)
						coefficients_A.append(m)
					
					#print(" linear_delay_wifa_pair", 2)
					x = [base_vector(cls.x[_i] for _i in range(block_size))]
					for n in range(1, memory_size + 1):
						x.append(base_vector(cls.s[n, _i] for _i in range(block_size)))
					
					#print(" linear_delay_wifa_pair", 3)
					y = [zero_v]
					for n in range(1, memory_size + 1):
						y.append(base_vector(cls.s[n, _i + block_size] for _i in range(block_size)))
					
					#print(" linear_delay_wifa_pair", 4)
					y0 = base_vector.zero(block_size)
					for n in range(memory_size + 1):
						y0 += base_matrix(coefficients_A[n]) @ x[n]
					y0 = y0.optimized()
					
					#print(" linear_delay_wifa_pair", 5)
					automaton_A = cls(output_transition=y0, state_transition=x[0] | y0)
					
					del x, y, y0
					
					#print(" linear_delay_wifa_pair", 6)
					matrix_A = dict()
					for i in range(memory_size + 1):
						for j in range(memory_size + 1):
							if i - j >= 0:
								matrix_A[i, j] = coefficients_A[i - j]
							else:
								matrix_A[i, j] = zero_m
					
					#print(" linear_delay_wifa_pair", 7)
					matrix_Ar = dict()
					for i in range(memory_size + 1):
						for j in range(memory_size):
							if i + j + 1 < memory_size + 1:
								matrix_Ar[i, j] = coefficients_A[i + j + 1]
							else:
								matrix_Ar[i, j] = zero_m
							#print("B:", i, j, matrix_Ar[i, j])
					
					if __debug__:
						def compare_coefficients():
							assert zero_m.is_zero()
							assert unit_m.is_one()
							assert zero_v.is_zero()
							
							for p in range(memory_size + 1):
								for q in range(memory_size + 1):
									c_A = zero_m[...]
									for k in range(memory_size + 1):
										try:
											c_A += matrix_P[p, k] @ matrix_A[k, q]
										except KeyError:
											pass
									
									try:
										assert c_A == matrix_PA[p, q]
									except KeyError:
										assert c_A == zero_m
					
					#print(" linear_delay_wifa_pair", 8)
					# `P` matrix calculation
					matrix_P = dict()
					for i in range(memory_size + 1):
						for j in range(memory_size + 1):
							if i != j:
								matrix_P[i, j] = zero_m[...]
							elif i == j:
								matrix_P[i, j] = unit_m[...]
					
					#print(" linear_delay_wifa_pair", 9)
					matrix_PA = dict()
					for i, j in matrix_A.keys():
						matrix_PA[i, j] = matrix_A[i, j][...]
					
					#print(" linear_delay_wifa_pair", 10)
					for i in reversed(range(memory_size + 1)):
						mm = []
						for p in range(i + 1):
							for q in range(p + 1):
								mm.append(matrix_PA[p, q])
						
						#print("-------------")
						pu = unit_m[...]
						mm.append(pu)
						
						matrix_PA[i, i].echelon(*mm)
						
						del mm
						
						for p in range(i + 1):
							for q in range(memory_size + 1):
								matrix_P[p, q] = pu @ matrix_P[p, q]
						
						for j in range(block_size):
							if matrix_PA[0, 0][j, :].is_zero():
								ll = j
								break
						else:
							ll = block_size
						
						psI_m = base_const_matrix.diagonal([base_ring.one() if _j <  ll else base_ring.zero() for _j in range(block_size)])
						psO_m = base_const_matrix.diagonal([base_ring.one() if _j >= ll else base_ring.zero() for _j in range(block_size)])
						
						matrix_Ps = dict()
						
						for p in range(i):
							for q in range(p + 1):
								for j in range(ll, block_size):
									matrix_PA[p, q][j, :] = matrix_PA[p + 1, q][j, :]
							for q in range(memory_size + 1):
								#print(" ::", i, p, q)
								matrix_Ps[p, q] = psI_m @ matrix_P[p, q] + psO_m @ matrix_P[p + 1, q]
						
						for q in range(i + 1):
							for j in range(ll, block_size):
								matrix_PA[i, q][j, :] = zero_v
						for q in range(memory_size + 1):
							matrix_Ps[i, q] = psI_m @ matrix_P[i, q] + psO_m @ matrix_P[0, q]
						
						for k, v in matrix_Ps.items():
							matrix_P[k] = v
						
						del matrix_Ps
						
					if __debug__:
						i = -1
						compare_coefficients()
					
					#print(" linear_delay_wifa_pair", 11)
					A00 = matrix_PA[0, 0]
					del matrix_PA
					
					#print()
					#for j in range(block_size):
					#	print(j, A00[j, :])
					
					#print(" linear_delay_wifa_pair", 12)
					for j in range(block_size):
						if A00[j, :].is_zero():
							#print(A00)
							raise BadLuck("Leading matrix not invertible, try again.")
					
					# TODO: check if delay is not too short
					
					#print(" linear_delay_wifa_pair", 13)
					A00_inv = A00.inverse()
					del A00
					
					#print(" linear_delay_wifa_pair", 14)
					coefficients_P = [A00_inv @ matrix_P[0, _j] for _j in range(memory_size + 1)]
					
					#print(" linear_delay_wifa_pair", 15)
					coefficients_Q = [zero_m]
					for q in range(memory_size):
						r = zero_m[...]
						for k in range(memory_size + 1):
							r += matrix_P[0, k] @ matrix_Ar[k, q]
						coefficients_Q.append(base_matrix(A00_inv @ r).optimized())
					
					del matrix_P, matrix_Ar
					
					if __debug__: # final check if the second function is really the inverse of the first function
						# input arguments
						arg_x = dict()
						for m in range(-memory_size, memory_size + 2):
							arg_x[m] = base_vector([base_vector.base_ring.var(('m' if m >= 0 else 'n') + '_' + str(abs(m)) + '_' + str(_i)) for _i in range(block_size)])
						
						# first function
						test_y = dict()
						for m in range(memory_size + 2):
							test_y[m] = base_vector.zero(block_size)
							for n in range(memory_size + 1):
								test_y[m] += base_matrix(coefficients_A[n]) @ arg_x[m - n] # substitute arguments
							test_y[m] = test_y[m].optimized()
						
						# second function
						test_x0 = base_vector.zero(block_size)
						for n in range(memory_size + 1):
							test_x0 -= base_matrix(coefficients_Q[n]) @ arg_x[-n] # substitute arguments
							test_x0 += base_matrix(coefficients_P[n]) @ test_y[n] # substitute the result of the first function into the second function
						test_x0 = test_x0.optimized()
						
						# TODO:
						#assert test_x0 == arg_x[0] # identity ?
					
					#print(" linear_delay_wifa_pair", 16)
					x = dict()
					for n in range(memory_size + 1):
						if n == 0:
							x[-n] = zero_v
						else:
							x[-n] = base_vector(cls.s[n, _i] for _i in range(block_size))
					
					#print(" linear_delay_wifa_pair", 17)
					y = dict()
					for n in range(memory_size + 1):
						if n == memory_size:
							y[n] = base_vector(cls.x[_i] for _i in range(block_size))
						else:
							y[n] = base_vector(cls.s[memory_size - n, _i + block_size] for _i in range(block_size))
					
					#print(" linear_delay_wifa_pair", 18)
					x0 = base_vector.zero(block_size)
					for n in range(memory_size + 1):
						x0 -= base_matrix(coefficients_Q[n]) @ x[-n]
						x0 += base_matrix(coefficients_P[n]) @ y[n]
					x0 = x0.optimized()
					
					#print(" linear_delay_wifa_pair", 19)
					s = x0 | y[memory_size]
					
					#print(" linear_delay_wifa_pair", 20)
					automaton_B = cls(output_transition=x0, state_transition=s)
					
					#print(" linear_delay_wifa_pair", "end")
					return automaton_A, automaton_B
				except BadLuck:
					print("bad luck")
					# TODO: reset entropy
					pass
		
		@classmethod
		def nonlinear_nodelay_wifa_pair(cls, block_size=8, memory_size=32):
			"Generate 2 nonlinear automata with 0 delay, respectively inverted. This algorithm has severe weakness, described in 'Break Finite Automata Public Key Cryptosystem' by Feng Bao and Yoshihide Igarashi."
			
			base_const_matrix = cls.base_const_matrix
			base_matrix = cls.base_matrix
			base_vector = cls.base_vector
			
			As, Ai = base_const_matrix.random_inverse_pair(block_size)
			coefficients_A = [None]
			coefficients_B = [None]
			coefficients_C = [None]
			for n in range(1, memory_size + 1):
				coefficients_A.append(base_const_matrix.random(block_size, block_size))
				coefficients_B.append(base_const_matrix.random(block_size, block_size))
				coefficients_C.append(base_const_matrix.random(block_size, block_size))
			
			arg = base_vector(cls.x[_i] for _i in range(block_size))
			
			x = [None]
			for n in range(1, memory_size + 2):
				x.append(base_vector(cls.s[n, _i] for _i in range(block_size)))
				if n == memory_size + 1:
					x.append(base_matrix(base_const_matrix.random(block_size, block_size)) @ base_vector(cls.s[n - 1, _i] for _i in range(block_size)))
			
			y = [None]
			for n in range(1, memory_size + 1):
				y.append(base_vector(cls.s[n, _i + block_size] for _i in range(block_size)))
			
			yr = base_matrix(As) @ arg
			for n in range(1, memory_size + 1):
				yr += base_matrix(coefficients_A[n]) @ x[n]
				yr += base_matrix(coefficients_B[n]) @ (x[n] & x[n + 1])
				yr += base_matrix(coefficients_C[n]) @ y[n]
			yr = yr.optimized()
			
			automaton_A = cls(output_transition=yr, state_transition=arg | yr)
			
			xr = base_matrix(Ai) @ arg
			for n in range(1, memory_size + 1):
				xr -= base_matrix(Ai @ coefficients_A[n]) @ x[n]
				xr -= base_matrix(Ai @ coefficients_B[n]) @ (x[n] & x[n + 1])
				xr -= base_matrix(Ai @ coefficients_C[n]) @ y[n]
			xr = xr.optimized()
			
			automaton_B = cls(output_transition=xr, state_transition=xr | arg)
			
			return automaton_A, automaton_B
		
		@classmethod
		def fapkc0(cls, block_size=8, memory_size=32):
			"Generate (public, private) pair of random FAPKC0 keys. WARNING: FAPKC0 is broken; do not use in production."
			
			ls, li = cls.linear_delay_wifa_pair(block_size=block_size, memory_size=memory_size)
			ns, ni = cls.nonlinear_nodelay_wifa_pair(block_size=block_size, memory_size=memory_size)
			
			straight = ns @ ls
			inverse = li @ ni
			
			return straight, inverse
		
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
	
	fqdn = '_Automaton_' + str(base_ring).replace('(', '_').replace(')', '_').replace('=', '_')
	Automaton.__qualname__ = fqdn
	globals()[fqdn] = Automaton
	
	return Automaton


if True or __debug__:
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
	
	def test_fapkc_encryption(Ring, block_size, stream_length, test_uncompiled=False, print_data=False):
		print("FAPKC encryption / decryption test")
		print(" algebra:", Ring, ", data block size =", block_size, ", stream length =", stream_length)
		
		Automaton = automaton_factory(Ring)
		ConstVector = Automaton.base_const_vector
		
		
		for memory_size in range(1, 33):
			print()
			print(" memory_size =", memory_size)
			text = [ConstVector.random(block_size) for i in range(stream_length)]
			print("  generating FAPKC0 key pair")
			start_time = time()
			encrypt, decrypt = Automaton.fapkc0(block_size=block_size, memory_size=memory_size)
			print("   time:", int(time() - start_time))
			
			if test_uncompiled:
				print("  encryption/decryption test")
				print("  encrypt... length =", stream_length)
				start_time = time()
				cipher_1 = list(encrypt(text))
				print("   time:", int(time() - start_time))
				if print_data:
					print(''.join(['{:02x}'.format(int(_x)) for _x in cipher_1]))
				
				print("  decrypt... length =", stream_length)
				start_time = time()
				text_1 = list(decrypt(cipher_1))
				print("   time:", int(time() - start_time))
				if print_data:
					print(''.join(['  '] * memory_size + ['{:02x}'.format(int(_x)) for _x in text]))
					print(''.join(['{:02x}'.format(int(_x)) for _x in text_1]))
				
				assert text_1[memory_size:] == text[:-memory_size]
			
			compiler = Compiler()
			with parallel(0):
				print("  compiling encrypt automaton")
				start_time = time()
				encrypt.compile('encrypt', compiler)
				print("   time:", int(time() - start_time))
				print("  compiling decrypt automaton")
				start_time = time()
				decrypt.compile('decrypt', compiler)
				print("   time:", int(time() - start_time))
			print("  code generation")
			code = compiler.compile()		
			encrypt = encrypt.wrap_compiled('encrypt', code)
			decrypt = decrypt.wrap_compiled('decrypt', code)
			print("   time:", int(time() - start_time))
			
			print("  testing compiled automata")
			with code:
				print("  encrypt... length =", stream_length)
				start_time = time()
				cipher_2 = list(encrypt(text))
				print("   time:", int(time() - start_time))
				if print_data:
					print(''.join(['{:02x}'.format(int(_x)) for _x in cipher_2]))
				
				print("  decrypt... length =", stream_length)
				start_time = time()
				text_2 = list(decrypt(cipher_2))
				print("   time:", int(time() - start_time))
				if print_data:
					print(''.join(['  '] * memory_size + ['{:02x}'.format(int(_x)) for _x in text]))
					print(''.join(['{:02x}'.format(int(_x)) for _x in text_2]))

	
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
		
		for i in range(1, 5):
			print()
			print(" round", i)
			print("  generating automata...")
			memory_size = i + 4
			#mixer, unmixer = Automaton.linear_nodelay_wifa_pair(block_size=block_size, memory_size=memory_size)
			mixer, unmixer = Automaton.fapkc0(block_size=block_size, memory_size=memory_size)
			plain_automaton = Automaton(Vector.random(dimension=block_size, variables=variables, order=3), Vector.random(dimension=memblock_size, variables=variables, order=3))
			
			print("  optimizing automata...")
			start_time = time()
			print(f"   mixer: {mixer.output_transition.circuit_size()} {mixer.state_transition.circuit_size()} {mixer.output_transition.dimension} {mixer.state_transition.dimension}")
			mixer.optimize()
			print(f"          {mixer.output_transition.circuit_size()} {mixer.state_transition.circuit_size()}")
			print(f"   unmixer: {unmixer.output_transition.circuit_size()} {unmixer.state_transition.circuit_size()} {unmixer.output_transition.dimension} {unmixer.state_transition.dimension}")
			unmixer.optimize()
			print(f"            {unmixer.output_transition.circuit_size()} {unmixer.state_transition.circuit_size()}")
			print(f"   plain: {plain_automaton.output_transition.circuit_size()} {plain_automaton.state_transition.circuit_size()} {plain_automaton.output_transition.dimension} {plain_automaton.state_transition.dimension}")
			plain_automaton.optimize()
			print(f"          {plain_automaton.output_transition.circuit_size()} {plain_automaton.state_transition.circuit_size()}")
			print("   time:", int(time() - start_time))
			
			print("  composing automata...")
			start_time = time()
			homo_automaton = mixer @ plain_automaton @ unmixer
			print("   time:", int(time() - start_time))
			print("  mixing states")
			start_time = time()
			homo_automaton.mix_states()
			print("   time:", int(time() - start_time))
			
			print("  optimizing automata...")
			start_time = time()
			print(f"   homomorphic: {homo_automaton.output_transition.circuit_size()} {homo_automaton.state_transition.circuit_size()} {homo_automaton.output_transition.dimension} {homo_automaton.state_transition.dimension}")
			print(f"                {[_circuit.circuit_size() for _circuit in homo_automaton.output_transition]} {[_circuit.circuit_size() for _circuit in homo_automaton.state_transition]}")
			homo_automaton.optimize()
			print(f"                {homo_automaton.output_transition.circuit_size()} {homo_automaton.state_transition.circuit_size()}")
			print(f"                {[_circuit.circuit_size() for _circuit in homo_automaton.output_transition]} {[_circuit.circuit_size() for _circuit in homo_automaton.state_transition]}")
			print("   time:", int(time() - start_time))
			
			print("  compiling automata...")
			start_time = time()
			compiler = Compiler()
			
			#try:
			#	Ring.compile_tables('RijndaelField', compiler)
			#except AttributeError:
			#	pass
			
			with parallel(0):
				mixer.compile('m', compiler)
				unmixer.compile('u', compiler)
				plain_automaton.compile('p', compiler)
				homo_automaton.compile('h', compiler)
			code = compiler.compile()
			
			#Path('automaton_' + str(i) + '.bc').write_bytes(code.modules[0].as_bitcode())
			
			mixer = mixer.wrap_compiled('m', code)
			unmixer = unmixer.wrap_compiled('u', code)
			plain_automaton = plain_automaton.wrap_compiled('p', code)
			homo_automaton = homo_automaton.wrap_compiled('h', code)
			print("   time:", int(time() - start_time))
			
			print("  encryption/decryption test...")
			text = list(automaton_input())
			start_time = time()
			with code:
				result1 = list(homo_automaton(text))
				result2 = list(mixer(plain_automaton(unmixer(text))))
			print("   actual:   ", ''.join(['{:02x}'.format(int(_ch)) for _ch in result1]))
			print("   predicted:", ''.join(['{:02x}'.format(int(_ch)) for _ch in result2]))
			assert result1 == result2
			print("   time:", int(time() - start_time))
	
	def automaton_test_suite(verbose=False):
		if verbose: print("running test suite")
		
		Automaton = automaton_factory(BooleanRing.get_algebra())
		Vector = Automaton.base_const_vector
		zero_v = Vector.zero(8)
		
		'''
		print()
		print("Testing nonlinear automata")
		for memory_size in range(1, 5):
			print()
			print("test for memory size", memory_size)
			print(" generating automata...")
			ls, li = Automaton.nonlinear_nodelay_wifa_pair(block_size=8, memory_size=memory_size)
			
			print(" compiling automata...")
			compiler = Compiler()
			with parallel(0):
				ls.compile('ls', compiler)
				li.compile('li', compiler)
			code = compiler.compile()
			ls = ls.wrap_compiled('ls', code)
			li = li.wrap_compiled('li', code)
			
			xi = [Vector.random(8) for _i in range(1024)]
			print(" xi =", ''.join(['{:02x}'.format(int(_x)) for _x in xi]))
			
			y = list(ls(xi))
			print(" y  =", ''.join(['{:02x}'.format(int(_x)) for _x in y]))
			
			xo = list(li(y))
			print(" xo =", ''.join(['{:02x}'.format(int(_x)) for _x in xo]))
			
			assert xi == xo
			print(" ok", memory_size)
		
		print()
		print("Testing linear automata")
		for memory_size in range(1, 5):
			print()
			print("test for memory size", memory_size)
			print(" generating automata...")
			ls, li = Automaton.linear_delay_wifa_pair(block_size=8, memory_size=memory_size)
			
			print(" compiling automata...")
			compiler = Compiler()
			with parallel(0):
				ls.compile('ls', compiler)
				li.compile('li', compiler)
			code = compiler.compile()
			ls = ls.wrap_compiled('ls', code)
			li = li.wrap_compiled('li', code)
			
			xi = [Vector.random(8) for _i in range(1024)]
			print(" xi =", ''.join(['{:02x}'.format(int(_x)) for _x in xi]))
			
			y = list(ls(xi + [Vector.random(8) for _i in range(memory_size)]))
			print(" y  =", ''.join(['{:02x}'.format(int(_x)) for _x in y]))
			
			xo = list(li(y))[memory_size:]
			print(" xo =", ''.join(['{:02x}'.format(int(_x)) for _x in xo]))
			
			assert xi == xo
			print(" ok", memory_size)
		'''
		
		print()
		print("Testing FAPKC0")
		for memory_size in range(1, 5):
			print()
			print("test for memory size", memory_size)
			print(" generating automata...")
			ls, li = Automaton.fapkc0(block_size=8, memory_size=memory_size)
			
			print(" composing identity automaton...")
			ll = ls @ li
			ll.optimize()
			print(ll.output_transition)
			print(ll.state_transition)
			
			print(" compiling automata...")
			compiler = Compiler()
			with parallel(0):
				ls.compile('ls', compiler)
				li.compile('li', compiler)
				ll.compile('ll', compiler)
			code = compiler.compile()
			ls = ls.wrap_compiled('ls', code)
			li = li.wrap_compiled('li', code)
			ll = ll.wrap_compiled('ll', code)
			
			xi = [Vector.random(8) for _i in range(1024)]
			print(" xi =", ''.join(['{:02x}'.format(int(_x)) for _x in xi]))
			
			y = list(ls(xi + [Vector.random(8) for _i in range(memory_size)]))
			print(" y  =", ''.join(['{:02x}'.format(int(_x)) for _x in y]))
			
			xo = list(li(y))[memory_size:]
			print(" xo =", ''.join(['{:02x}'.format(int(_x)) for _x in xo]))
			
			assert xi == xo, "Encryption / decryption test failed."
			
			print(" testing identity automaton...")
			xr = list(ll(xi + [Vector.random(8) for _i in range(memory_size)]))[memory_size:]
			assert xi == xr, "Identity automaton test failed."
			
			print(" ok")
			
		
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



if __name__ == '__main__':
	with parallel():
		#test_fapkc_encryption(BooleanRing.get_algebra(), 8, 64, print_data=True)
		test_homomorphic_encryption(BooleanRing.get_algebra(), 8, 8, 128)


quit()

if __name__ == '__main__':
	import pycallgraph
	import pycallgraph.output.graphviz
	profiler = pycallgraph.PyCallGraph(output=pycallgraph.output.graphviz.GraphvizOutput(output_file='automaton.png'))
	
	Automaton = automaton_factory(BooleanRing.get_algebra())
	Vector = Automaton.base_const_vector
	Matrix = Automaton.base_const_matrix
	Polynomial = Automaton.base_polynomial
	
	'''
	#a = Matrix.random(64, 64)
	#b = Matrix.random(64, 64)
	print(__debug__)

	#one = Polynomial.one()
	#s_1_5, s_2_5, s_1_6, s_2_6, s_2_7, s_1_1, s_2_0, s_2_1, x_0 = [Polynomial.var(_x) for _x in ['s_1_5', 's_2_5', 's_1_6', 's_2_6', 's_2_7', 's_1_1', 's_2_0', 's_2_1', 'x_0']]
	#p = (s_1_5 * (s_2_5 + one)) + s_1_6 + s_2_5 + s_2_6 + s_2_7 + (s_1_1 + s_2_0) + (s_1_1 + s_2_0 + s_2_1 + x_0)
	#
	#print(p)
	#q = p.optimized()
	#print(q)
	#assert p == q
	#quit()
	
	#m = Matrix.unit(16)
	#n = m[...]
	
	block_size = 8
	memory_size = 2
	encrypt, decrypt = Automaton.fapkc0(block_size=block_size, memory_size=memory_size)
	print("encrypt automaton size:", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
	with parallel():
		encrypt.optimize()
	print("encrypt automaton size:", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
	profiler.start()
	print("mixing states")
	encrypt.mix_states()
	profiler.done()
	#print("encrypt automaton size:", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
	#with parallel():
	#	encrypt.optimize()
	#print("encrypt automaton size:", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
	quit()
	
	
	#profiler.start()
	#encrypt = encrypt.optimized()
	#profiler.done()
	
	#quit()
	
	#a, b = Automaton.random_nonlinear_equation_pair(10)
	#print(a)
	#print(b)
	#quit()
	'''
	
	memory_size = 4
	block_size = 8
	
	text = [Vector.random(block_size) for _i in range(64)]
	
	print("generating FAPKC0 key pair", block_size, memory_size)
	encrypt, decrypt = Automaton.fapkc0(block_size=block_size, memory_size=memory_size)
	print()
	print("encrypt automaton size", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
	print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
	print("decrypt automaton size", decrypt.output_transition.circuit_size(), decrypt.state_transition.circuit_size())
	print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
	#print(encrypt.output_transition)
	#print(encrypt.state_transition)
	#print(decrypt.output_transition)
	#print(decrypt.state_transition)
	print("encryption/decryption test")
	encrypted1 = list(encrypt(text))
	decrypted1 = list(decrypt(encrypted1))
	print(''.join(['  '] * memory_size + ['{:02x}'.format(int(_x)) for _x in text]))
	print(''.join(['{:02x}'.format(int(_x)) for _x in decrypted1]))
	assert decrypted1[memory_size:] == text[:-memory_size]
	
	'''
	print()
	print("optimization pass...")
	encrypt.optimize()
	decrypt.optimize()
	print("encrypt automaton size", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
	print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
	print("decrypt automaton size", decrypt.output_transition.circuit_size(), decrypt.state_transition.circuit_size())
	print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
	#print(encrypt.output_transition)
	#print(encrypt.state_transition)
	#print(decrypt.output_transition)
	#print(decrypt.state_transition)
	print("encryption/decryption test")
	encrypted2 = list(encrypt(text))
	decrypted2 = list(decrypt(encrypted2))
	print(f"{['{:02x}'.format(_x) for _x in decrypted2]}, {['{:02x}'.format(_x) for _x in text]}")
	assert decrypted2[memory_size:] == text[:-memory_size]
	assert encrypted2 == encrypted1
	'''
	
	print()
	print("obfuscating states...")
	with parallel():
		encrypt.mix_states()
		decrypt.mix_states()
	print("encrypt automaton size", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
	print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
	print("decrypt automaton size", decrypt.output_transition.circuit_size(), decrypt.state_transition.circuit_size())
	print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
	
	#compiler = Compiler()
	#with parallel(0):
	#	print("compiling encrypt automaton")
	#	encrypt.compile('encrypt', compiler)
	#	print("compiling decrypt automaton")
	#	decrypt.compile('decrypt', compiler)
	#code = compiler.compile()		
	#encrypt_c = encrypt.wrap_compiled('encrypt', code)
	#decrypt_c = decrypt.wrap_compiled('decrypt', code)
	
	#print("encryption/decryption test")
	#encrypted3 = list(encrypt_c([int(_x) for _x in text]))
	#decrypted3 = list(decrypt_c(encrypted3))
	#print(''.join(['{:02x}'.format(_x) for _x in decrypted3]))
	#print(''.join(['  '] * memory_size + ['{:02x}'.format(int(_x)) for _x in text]))
	#assert decrypted3[memory_size:] == text[:-memory_size]
	#assert encrypted3 == encrypted1
	
	print()
	print("optimization pass...")
	with parallel():
		encrypt.optimize()
		decrypt.optimize()
	print("encrypt automaton size", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
	print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
	print("decrypt automaton size", decrypt.output_transition.circuit_size(), decrypt.state_transition.circuit_size())
	print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
	#print(encrypt.output_transition)
	#print(decrypt.output_transition)
	
	compiler = Compiler()
	with parallel(0):
		print("compiling encrypt automaton")
		encrypt.compile('encrypt', compiler)
		print("compiling decrypt automaton")
		decrypt.compile('decrypt', compiler)
	code = compiler.compile()		
	encrypt_c = encrypt.wrap_compiled('encrypt', code)
	decrypt_c = decrypt.wrap_compiled('decrypt', code)
	
	print("encryption/decryption test")
	encrypted4 = list(encrypt_c(text))
	decrypted4 = list(decrypt_c(encrypted4))
	print(''.join(['  '] * memory_size + ['{:02x}'.format(int(_x)) for _x in text]))
	print(''.join(['{:02x}'.format(int(_x)) for _x in decrypted4]))
	assert decrypted4[memory_size:] == text[:-memory_size]
	assert encrypted4 == encrypted1
	
	
	quit()
	
	
	#automaton_test_suite(verbose=True)
	
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
	#	test_homomorphic_encryption(BooleanRing.get_algebra(), 8, 4, 32)
		test_homomorphic_encryption(RijndaelField.get_algebra(), 1, 1, 64)
	
	#Automaton = automaton_factory(BooleanRing.get_algebra())
	#Vector = Automaton.base_vector
	
	#cd10a = Automaton.countdown_gadget(ticks=10, prefix=True)
	#cd10b = Automaton.countdown_gadget(ticks=10, prefix=False)
	
	#input_stream = [Vector(_n, dimension=8) for _n in range(20)]
	#print(list(int(_x) for _x in cd10a(input_stream)))
	#print(list(int(_x) for _x in cd10b(input_stream)))
	
