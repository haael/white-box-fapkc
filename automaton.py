#!/usr/bin/python3
#-*- coding:utf8 -*-


from collections import deque
from itertools import product

from utils import memoize
from rings import *
from polynomial import *
from linear import *


__all__ = 'automaton_factory',


def automaton_factory(base_ring):
	base_polynomial = Polynomial.get_algebra(base_ring=base_ring)
	base_vector = Vector.get_algebra(base_ring=base_polynomial)
	base_matrix = Matrix.get_algebra(base_ring=base_polynomial)
	
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
		
		@memoize
		def memory_size(self):
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
		
		@classmethod
		def countdown_gadget(cls, block_size=8, ticks=32, prefix=True):
			x = base_vector(cls.x[_i] for _i in range(block_size))
			s = base_vector(cls.s[1, _i] for _i in range(block_size))
			
			set_point = base_vector(ticks, dimension=block_size)
			
			in_switch = base_ring.zero()
			for i in range(block_size):
				in_switch |= (s[i] - set_point[i])
				in_switch = in_switch.canonical()
			
			def add(a, b, c):
				return a + b + c, a * b | b * c | c * a
			
			bsum = []
			c = base_ring.zero()
			for i in range(block_size):
				r, c = add(s[i], (in_switch if i == 0 else base_ring.zero()), c.canonical())
				bsum.append(r)
			state_transition = base_vector(bsum)
			
			out_switch = base_ring.zero()
			for i in range(block_size):
				out_switch |= (s[i] - set_point[i])
				out_switch = out_switch.canonical()
			out_switch = (base_ring.zero() if prefix else base_ring.one()) - out_switch
			output_transition = x * out_switch
			
			return cls(output_transition=output_transition.canonical(), state_transition=state_transition.canonical())
		
		@classmethod
		def state_initialization_gadget(cls, block_size=8, memory_size=32):
			state_transition = base_vector(cls.x[_i] for _i in range(block_size))
			output_transition = base_vector.zero(block_size)
			return cls(output_transition=output_transition.canonical(), state_transition=state_transition.canonical())
		
		@classmethod
		def linear_nodelay_wifa_pair(cls, block_size=8, memory_size=32):
			"Returns a pair of linear finite automata with 0 delay, being their respective inverses."
			
			x = base_vector(cls.x[_i] for _i in range(block_size))
			s = [None]
			for n in range(1, memory_size + 1):
				s.append(base_vector(cls.s[n, _i] for _i in range(block_size)))
			
			ms, mi = base_matrix.random_inverse_pair(block_size)
			
			ya = ms @ x
			yb = mi @ x
			for n in range(1, memory_size + 1):
				m = base_matrix.random(block_size, block_size)
				ya += m @ s[n]
				yb -= m @ mi @ s[n]
			
			ya = ya.canonical()
			yb = yb.canonical()
			
			automaton_A = cls(output_transition=ya, state_transition=x)
			automaton_B = cls(output_transition=yb, state_transition=yb)
			return automaton_A, automaton_B
		
		@classmethod
		def linear_delay_wifa_pair(cls, block_size=8, memory_size=32):
			class BadLuck(BaseException):
				pass
			
			while True:
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
					
					automaton_A = cls(output_transition=y.canonical(), state_transition=x[0])
					
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
					
					coefficients_P = [(A00_inv @ matrix_P[0, _j]).canonical() for _j in range(memory_size + 1)]
					
					coefficients_Q = [zero_m]
					for q in range(1, memory_size + 1):
						r = zero_m[...]
						for k in range(memory_size + 1):
							r += matrix_P[0, k] @ (coefficients_A[k + q][...] if (k + q < memory_size) else zero_m[...]) # FIXME: correct?
						coefficients_Q.append((A00_inv @ r).canonical())
					
					x = [base_vector.zero(block_size)]
					y = [base_vector(cls.x[_i] for _i in range(block_size))]
					
					for n in range(1, memory_size + 1):
						x.append(base_vector(cls.s[n, _i] for _i in range(block_size)))
						y.append(base_vector(cls.s[n, _i + block_size] for _i in range(block_size)))
					
					x0 = zero_v[:]
					for n in range(memory_size + 1):
						x0 += coefficients_Q[n] @ x[n]
						x0 += coefficients_P[n] @ y[-n]
					x[0] = x0.canonical()
					
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
		
		def transition(self, x, history):
			"""
			Takes the input symbol `x` (vector of Galois fields)
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
			while len(history) > self.memory_size():
				history.pop()
			return y
		
		def __call__(self, in_stream):
			"Takes the stream of input symbols, yields the stream of output symbols. Starts from the state composed of zero vectors."
			history = deque([base_vector.zero(len(self.state_transition))] * self.memory_size()) # initial state
			for x in in_stream:
				yield self.transition(x, history)
		
		def __matmul__(self, other):
			"Automaton composition."
			
			shift = len(other.state_transition)
			
			substitution = {}
			for i, yi in enumerate(other.output_transition):
				substitution[str(self.x[i])] = yi
			for t in range(self.memory_size()):
				for i in range(len(self.state_transition)):
					substitution[str(self.s[t + 1, i])] = self.s[t + 1, i + shift]
			
			output_transition = base_vector(_trans(**substitution) for _trans in self.output_transition).canonical()
			state_transition = base_vector(chain(other.state_transition, (_trans(**substitution) for _trans in self.state_transition))).canonical()
			
			return self.__class__(output_transition, state_transition)
	
	Automaton.base_ring = base_ring
	Automaton.base_polynomial = base_polynomial
	Automaton.base_vector = base_vector
	Automaton.base_matrix = base_matrix
	
	return Automaton


if __debug__:
	import pickle
	from itertools import chain
	
	def test_automaton(Ring):
		zero = Ring.zero()
		one = Ring.one()
		
		Automaton = automaton_factory(Ring)
		Vector = Automaton.base_vector
		
		x = Vector([Automaton.x[_i] for _i in range(8)])
		s_1_0 = Automaton.s[1, 0]
		
		automaton_input = [Vector([one, zero]), Vector([zero, zero]), Vector([one, zero]), Vector([zero, one]), Vector([zero, zero]), Vector([zero, zero]), Vector([zero, one]), Vector([one, one])]
		
		automaton1 = Automaton(Vector([x[1], x[0]]), Vector([], base_ring=Ring))
		automaton2 = automaton1 @ automaton1
		assert list(automaton2(automaton_input)) == list(automaton1(automaton1(automaton_input)))
		
		automaton3 = Automaton(Vector([x[1], s_1_0]), Vector([x[0]]))
		automaton4 = automaton1 @ automaton3
		assert list(automaton4(automaton_input)) == list(automaton1(automaton3(automaton_input)))
		
		adder = Automaton(Vector([x[0] + x[1] + s_1_0, x[1], x[2], x[3], x[4], x[5], x[6], x[7]]), Vector([x[0] * x[1] | x[0] * s_1_0 | x[1] * s_1_0]))
		
		mixer_input = [Vector.random(8) for _i in range(256)]
		
		for mo in (0, 7):
			print("testing automaton of memory order", mo)
			mixer, unmixer = Automaton.linear_nodelay_wifa_pair(block_size=8, memory_size=mo)
			
			mixer_output = list(mixer(mixer_input))
			mixer_recode = list(unmixer(mixer_output))
			
			assert mixer_input == mixer_recode, "memory_size = {}".format(mo)
			
			encoded_input1 = list((mixer @ adder)(mixer_input))
			encoded_input2 = list(mixer(adder(mixer_input)))
			
			assert encoded_input1 == encoded_input2, "memory_size = {}".format(mo)
			
			plain_output = list(adder(mixer_input))
			homo_output = list(unmixer(encoded_input1))
			
			assert plain_output == homo_output
	
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
			test_automaton(ring)
		'''
		
		if verbose: print()
		if verbose: print("test BooleanRing()")
		ring = BooleanRing.get_algebra()
		if verbose: print(" automaton test")
		test_automaton(ring)
		
		'''
		for i in (2, 3, 4, 5, 16, 64, 128, 512, 1024):
			if verbose: print()
			if verbose: print("test GaloisRing(size={})".format(i))
			field = GaloisField.get_algebra(size=i)
			if verbose: print(" automaton test")
			test_automaton(field)
		
		assert BinaryRing.get_algebra(exponent=1)(1) != RijndaelRing(1)
		
		for i in (2, 3, 4, 5, 8, 9, 10):
			if verbose: print()
			if verbose: print("test BinaryRing(exponent={})".format(i))
			field = BinaryRing.get_algebra(exponent=i)
			if verbose: print(" automaton test")
			test_automaton(field)
		'''
		
		if verbose: print()
		if verbose: print("test RijndaelField()")
		field = RijndaelField
		if verbose: print(" automaton test")
		test_automaton(field)
		
	__all__ = __all__ + ('test_automaton', 'automaton_test_suite',)


if __debug__ and __name__ == '__main__':
	#automaton_test_suite(verbose=True)


	Automaton = automaton_factory(BooleanRing.get_algebra())
	Vector = Automaton.base_vector
	
	cd10a = Automaton.countdown_gadget(ticks=10, prefix=True)
	cd10b = Automaton.countdown_gadget(ticks=10, prefix=False)
	
	input_stream = [Vector(_n, dimension=8) for _n in range(20)]
	print(list(int(_x) for _x in cd10a(input_stream)))
	print(list(int(_x) for _x in cd10b(input_stream)))



