#!/usr/bin/python3


__all__ = 'LinearCircuit', 'QuadraticCircuit', 'Automaton'


from itertools import product, chain
from collections import defaultdict

from linear import *
from utils import superscript, cached, table_fallback


class LinearCircuit:
	"Circuit performing only linear operations on its arguments. Takes a vector of elements of Galois field, returns a vector. Can be added, subtracted and composed with another linear circuit."
	
	@property
	@cached
	def Field(self):
		return self[0, 0].Field
	
	@property
	@cached
	def Linear(self):
		return self[0, 0].Linear
	
	@property
	@cached
	def Array(self):
		return self[0, 0].Array
	
	@property
	@cached
	def Table(self):
		return table_fallback(self.__functions.__class__)
	
	@classmethod
	def random(cls, output_size, input_size, Table, Array, Linear, Field, randbelow):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), Linear.random(Array, Field, randbelow)) for (_m, _n) in product(range(output_size), range(input_size))), [output_size, input_size], [Field.field_power, None], [Linear, Field], Array=Array))
	
	@classmethod
	def shift(cls, position, output_size, input_size, Table, Array, Linear, Field):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), Linear.one(Array, Field) if _m + position == _n else Linear.zero(Array, Field)) for (_m, _n) in product(range(output_size), range(input_size))), [output_size, input_size], [Field.field_power, None], [Linear, Field], Array=Array))
	
	def __init__(self, functions, output_size=None, input_size=None):
		if output_size is not None:
			self.output_size = output_size
		else:
			self.output_size = len(set(_a for (_a, _b) in functions.keys()))
		
		if input_size is not None:
			self.input_size = input_size
		else:
			self.input_size = len(set(_b for (_a, _b) in functions.keys()))
		
		self.__functions = functions
	
	def serialize(self):
		try:
			return self.__functions.serialize()
		except AttributeError:
			return chain.from_iterable(_v.serialize() for _v in self.__functions)
	
	def __getitem__(self, index):
		try:
			m, n = index
		except ValueError:
			raise TypeError("LinearCircuit.__getitem__ expects 2 numeric indices.")
		
		return self.__functions[m, n]
	
	def __call__(self, args):
		if len(args) != self.input_size:
			raise ValueError(f"Input size {self.input_size} does not match circuit requirements ({len(args)}).")
		
		return args.__class__(args.Array((self.Field.sum(self[m, k](args[k]) for k in range(self.input_size)) for m in range(self.output_size)), [None], [self.Field]))
	
	def __add__(self, other):
		"Sum of two linear circuits: `(a + b)(x) = a(x) + b(x)`."
		
		if self.input_size != other.input_size:
			raise ValueError("Input sizes of linear circuits to add should be the same.")
		
		if self.output_size != other.output_size:
			raise ValueError("Output sizes of linear circuits to add should be the same.")
		
		try:
			return self.__class__(self.Table((((m, n), self[m, n] + other[m, n]) for n in range(self.input_size) for m in range(self.output_size)), [self.output_size, self.input_size], [self.Field.field_power, None], [self.Linear, self.Field], Array=self.Array))
		except TypeError:
			return NotImplemented
	
	def __sub__(self, other):
		"Difference of two linear circuits: `(a - b)(x) = a(x) - b(x)`"
		
		if self.input_size != other.input_size:
			raise ValueError("Input sizes of linear circuits to subtract should be the same.")
		
		if self.output_size != other.output_size:
			raise ValueError("Output sizes of linear circuits to subtract should be the same.")
		
		try:
			return self.__class__(self.Table((((m, n), self[m, n] - other[m, n]) for n in range(self.input_size) for m in range(self.output_size)), [self.output_size, self.input_size], [self.Field.field_power, None], [self.Linear, self.Field], Array=self.Array))
		except TypeError:
			return NotImplemented
	
	def __neg__(self):
		try:
			return self.__class__(self.Table((((m, n), -self[m, n]) for n in range(self.input_size) for m in range(self.output_size)), [self.output_size, self.input_size], [self.Field.field_power, None], [self.Linear, self.Field], Array=self.Array))
		except TypeError:
			return NotImplemented
	
	def __matmul__(self, other):
		"Composition of two linear circuits: `(a @ b)(x) = a(b(x))`."
		
		if self.input_size != other.output_size:
			raise ValueError(f"Input size of the left circuit (got {self.input_size}) should match output size of the right circuit (got {other.output_size}).")
		
		try:
			return self.__class__(self.Table((((m, n), sum((self[m, k] @ other[k, n] for k in range(self.input_size)), self.Linear.zero(self.Array, self.Field))) for n in range(other.input_size) for m in range(self.output_size)), [self.output_size, other.input_size], [self.Field.field_power, None], [self.Linear, self.Field], Array=self.Array))
		except TypeError:
			return NotImplemented
	
	def __mul__(self, other):
		"Composition of linear circuit with linear operation (right hand): `(a * l)(x) = a(Vector(l(xi) for xi in x))`."
		return self.__class__(self.Table((((m, n), (self[m, n] @ other)) for n in range(self.input_size) for m in range(self.output_size)), [self.output_size, self.input_size], [self.Field.field_power, None], [self.Linear, self.Field], Array=self.Array))
	
	def __rmul__(self, other):
		"Composition of linear circuit with linear operation (left hand): `(l * a)(x) = Vector(l(xi) for xi in a(x))`."
		return self.__class__(self.Table((((m, n), (other @ self[m, n])) for n in range(self.input_size) for m in range(self.output_size)), [self.output_size, self.input_size], [self.Field.field_power, None], [self.Linear, self.Field], Array=self.Array))
	
	def __shl__(self, p):
		position, length = p
		return self @ self.shift(position, self.input_size, length)
	
	def print_matrix(self):
		for m in range(self.output_size):
			for k in range(self.Field.field_power):
				r = []
				for n in range(self.input_size):
					r.append(self[m, n].linear_coefficient(k))
				print(" ".join([str(_r) for _r in r]))
			print()


class QuadraticCircuit:
	"Circuit performing quadratic operations on pairs of its arguments. Takes a vector of elements of Galois field, returns a vector. Can be added and subtracted with another quadratic circuit. Can be composed with linear circuit."
	
	@property
	@cached
	def Field(self):
		return self[0, 0, 0].Field	
	
	@property
	@cached
	def Linear(self):
		return self[0, 0, 0].Linear
	
	@property
	@cached
	def Quadratic(self):
		return self[0, 0, 0].Quadratic
	
	@property
	@cached
	def Array(self):
		return self[0, 0, 0].Array
	
	@property
	@cached
	def Table(self):
		return table_fallback(self.__functions.__class__)
	
	@classmethod
	def random(cls, output_size, input_size, Table, Array, Quadratic, Linear, Field, randbelow):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n, _o), Quadratic.random(Array, Linear, Field, randbelow)) for (_m, _n, _o) in product(range(output_size), range(input_size), range(input_size))), [output_size, input_size, input_size], [Field.field_power, Field.field_power, None], [Quadratic, Linear, Field], Array=Array))
	
	def __init__(self, functions, output_size=None, input_size=None):
		if output_size is not None:
			self.output_size = output_size
		else:
			self.output_size = len(set(_a for (_a, _b, _c) in functions.keys()))
		
		if input_size is not None:
			self.input_size = input_size
		else:
			self.input_size = len(set(_b for (_a, _b, _c) in functions.keys()))
		
		self.__functions = functions
	
	def serialize(self):
		try:
			return self.__functions.serialize()
		except AttributeError:
			return chain.from_iterable(_v.serialize() for _v in self.__functions)
	
	def __getitem__(self, index):
		try:
			m, n, o = index
		except ValueError:
			raise TypeError("QuadraticCircuit.__getitem__ expects 3 numeric indices.")
		
		return self.__functions[m, n, o]
	
	def __call__(self, args):
		return args.__class__(args.Array((self.Field.sum(self[m, k, l](args[k], args[l]) for (k, l) in product(range(self.input_size), range(self.input_size))) for m in range(self.output_size)), [None], [self.Field]))
	
	def __add__(self, other):
		"Sum of two quadratic circuits: `(a + b)(x) = a(x) + b(x)`."
		if self.input_size != other.input_size: raise ValueError(f"Input sizes of quadratic circuits to add should be the same (got {self.input_size} vs. {other.input_size}).")
		if self.output_size != other.output_size: raise ValueError(f"Output sizes of quadratic circuits to add should be the same (got {self.output_size} vs. {other.output_size}).")
		return self.__class__(self.Table((((m, n, o), self[m, n, o] + other[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size))), [self.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __sub__(self, other):
		"Difference of two quadratic circuits: `(a - b)(x) = a(x) - b(x)`"
		if self.input_size != other.input_size: raise ValueError(f"Input sizes of quadratic circuits to subtract should be the same (got {self.input_size} vs. {other.input_size}).")
		if self.output_size != other.output_size: raise ValueError(f"Output sizes of quadratic circuits to subtract should be the same (got {self.output_size} vs. {other.output_size}).")
		return self.__class__(self.Table((((m, n, o), self[m, n, o] - other[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size))), [self.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __neg__(self):
		return self.__class__(self.Table((((m, n, o), -self[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size))), [self.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __matmul__(self, other):
		"Composition of a quadratic circuit with a linear one. Linear is applied first, quadratic next: `(q @ l)(x) = q(l(x))`. Result is a quadratic circuit."
		if self.input_size != other.output_size: raise ValueError(f"Input size of left automaton (got {self.input_size}) must match output size of the right automaton (got {other.output_size}).")
		return self.__class__(self.Table((((q, i, j), sum((self[q, o, p] @ (other[o, i], other[p, j]) for o in range(self.input_size) for p in range(self.input_size)), self.Quadratic.zero(self.Array, self.Linear, self.Field))) for q in range(self.output_size) for i in range(other.input_size) for j in range(other.input_size)), [self.output_size, other.input_size, other.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __rmatmul__(self, other):
		"Composition of a linear circuit with a quadratic one. Quadratic is applied first, linear next: `(l @ q)(x) = l(q(x))`. Result is a quadratic circuit."
		if self.output_size != other.input_size: raise ValueError(f"Output size of right automaton (got {self.output_size}) must match input size of the left automaton (got {other.input_size}).")
		return self.__class__(self.Table((((a, c, d), sum((other[a, b] @ self[b, c, d] for b in range(self.output_size)), self.Quadratic.zero(self.Array, self.Linear, self.Field))) for a in range(other.output_size) for c in range(self.input_size) for d in range(self.input_size)), [other.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __mul__(self, other):
		"Composition of quadratic circuit with linear operation (right hand): `(a * l)(x) = a(Vector([l(xi) for xi in x]))`."
		return self.__class__(self.Table((((m, n, o), self[m, n, o] @ (other, other)) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size))), [self.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __rmul__(self, other):
		"Composition of quadratic circuit with linear operation (left hand): `(l * a)(x) = Vector([l(xi) for xi in a(x)])`."
		return self.__class__(self.Table((((m, n, o), other @ self[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size))), [self.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))


class Automaton:
	@classmethod
	def random_linear_linear(cls, output_size, input_size, state_size, Dictionary, Array, Vector, LinearCircuit, Linear, Field, randbelow):
		out_transition = LinearCircuit.random(output_size, input_size + state_size, Dictionary, Array, Linear, Field, randbelow)
		state_transition = LinearCircuit.random(state_size, input_size + state_size, Dictionary, Array, Linear, Field, randbelow)
		init_state = Vector.random(state_size, Array, Field, randbelow)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def random_linear_quadratic(cls, output_size, input_size, state_size, Dictionary, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randbelow):
		out_transition = LinearCircuit.random(output_size, input_size + state_size, Dictionary, Array, Linear, Field, randbelow)
		state_transition = QuadraticCircuit.random(state_size, input_size + state_size, Dictionary, Array, Quadratic, Linear, Field, randbelow)
		init_state = Vector.random(state_size, Array, Field, randbelow)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def random_quadratic_linear(cls, output_size, input_size, state_size, Dictionary, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randbelow):
		out_transition = QuadraticCircuit.random(output_size, input_size + state_size, Dictionary, Array, Quadratic, Linear, Field, randbelow)
		state_transition = LinearCircuit.random(state_size, input_size + state_size, Dictionary, Array, Linear, Field, randbelow)
		init_state = Vector.random(state_size, Array, Field, randbelow)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def random_quadratic_quadratic(cls, output_size, input_size, state_size, Dictionary, Array, Vector, QuadraticCircuit, Quadratic, Linear, Field, randbelow):
		out_transition = QuadraticCircuit.random(output_size, input_size + state_size, Dictionary, Array, Quadratic, Linear, Field, randbelow)
		state_transition = QuadraticCircuit.random(state_size, input_size + state_size, Dictionary, Array, Quadratic, Linear, Field, randbelow)
		init_state = Vector.random(state_size, Array, Field, randbelow)
		return cls(out_transition, state_transition, init_state)
	
	def __init__(self, out_transition, state_transition, init_state):
		self.out_transition = out_transition
		self.state_transition = state_transition
		self.init_state = init_state
	
	def __call__(self, stream, state=None):
		if state is None:
			state = self.init_state[:]
		
		for word in stream:
			yield self.out_transition(word | state)
			state[:] = self.state_transition(word | state)
	
	def __matmul__(self, other):
		out_transition = self.out_transition @ (other.out_transition | shift_state)
		state_transition = (self.state_transition @ other.out_transition) | other.state_transition
		init_state = other.state_transition | self.state_transition
		return self.__class__(out_transition, state_transition, init_state)


class MemoryAutomaton:
	@classmethod
	def random_linear(cls, block_size, delay, Dictionary, Array, Vector, LinearCircuit, Linear, Field, randbelow):
		word_transition = LinearCircuit.random(block_size, block_size, Dictionary, Array, Linear, Field, randbelow)
		in_transition = LinearCircuit.random(block_size, block_size * delay, Dictionary, Array, Linear, Field, randbelow)
		out_transition = LinearCircuit.random(block_size, block_size * delay, Dictionary, Array, Linear, Field, randbelow)
		in_state = Vector.random(block_size * delay, Array, Field, randbelow)
		out_state = Vector.random(block_size * delay, Array, Field, randbelow)
		return cls(word_transition, in_transition, out_transition, in_state, out_state)
	
	@classmethod
	def random_quadratic(cls, block_size, delay, Dictionary, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randbelow):
		word_transition = LinearCircuit.random(block_size, block_size, Dictionary, Array, Linear, Field, randbelow)
		in_transition = QuadraticCircuit.random(block_size, block_size * delay, Dictionary, Array, Quadratic, Linear, Field, randbelow)
		out_transition = QuadraticCircuit.random(block_size, block_size * delay, Dictionary, Array, Quadratic, Linear, Field, randbelow)
		in_state = Vector.random(block_size * delay, Array, Field, randbelow)
		out_state = Vector.random(block_size * delay, Array, Field, randbelow)
		return cls(word_transition, in_transition, out_transition, in_state, out_state)
	
	def __init__(self, word_transition, in_transition, out_transition, in_init_state, out_init_state):
		self.word_transition = word_transition
		self.in_transition = in_transition
		self.out_transition = out_transition
		self.in_init_state = in_init_state
		self.out_init_state = out_init_state
	
	def __call__(self, stream, in_state=None, out_state=None):
		if in_state is None:
			in_state = self.in_init_state[:]
		
		if out_state is None:
			out_state = self.out_init_state[:]
		
		for word in stream:
			result = self.word_transition(word)
			
			if self.in_transition is not None:
				result += self.in_transition(in_state)
			
			if self.out_transition is not None:
				result += self.out_transition(out_state)
			
			yield result
			
			in_state = (word | in_state)[:-len(word)]
			out_state = (result | out_state)[:-len(result)]
	
	def __matmul__(self, other):
		#mid = other.word_transition(in_) + other.in_transition(in_state) + other.out_transition(mid_state)
		#out = self.word_transition(mid) + self.in_transition(mid_state) + self.out_transition(out_state)
		
		if not other.out_transition and not self.in_transition:
			#mid = other.word_transition(in_) + other.in_transition(in_state)
			#out = self.word_transition(mid) + self.out_transition(out_state)
			return self.__class__(self.word_transition @ other.word_transition, self.word_transition @ other.in_transition, self.out_transition)
		
		elif not other.out_transition:
			#mid = other.word_transition(in_) + other.in_transition(in_state)
			#out = self.word_transition(mid) + self.in_transition(mid_state) + self.out_transition(out_state)
			
			mid_state_trn = LinearCircuit.zero(0, 2 * other.in_transition.input_size)
			for i in range(0, self.in_transition.input_size, other.word_transition.input_size):
				#mid_state_trn |= other.word_transition @ LinearCircuit.shift(i, other.word_transition.input_size, 2 * other.in_transition.input_size) + other.in_transition @ LinearCircuit.shift(i + other.word_transition.input_size, other.in_transition.input_size, 2 * other.in_transition.input_size)
				mid_state_trn |= other.word_transition << (i, 2 * other.in_transition.input_size) + other.in_transition << (i + other.word_transition.input_size, 2 * other.in_transition.input_size)
			
			#in_transition = self.word_transition @ other.in_transition @ LinearCircuit.shift(0, other.in_transition.input_size, 2 * other.in_transition.input_size) + self.in_transition @ mid_state_trn
			in_transition = self.word_transition @ other.in_transition << (0, 2 * other.in_transition.input_size) + self.in_transition @ mid_state_trn
			
			return self.__class__(self.word_transition @ other.word_transition, in_transition, self.out_transition)
		
		else:
			raise NotImplementedError

	'''	
	
	sum(M[k](i[k])) = sum(N[l](o[l]))
	
	M[0] @ i[0] + M[1] @ i[1] + M[2] @ i[2] + M[3] @ i[3] = N[0] @ o[0] + N[1] @ o[1] + N[2] @ o[2] + N[3] @ o[3]
	M[0] @ i[1] + M[1] @ i[2] + M[2] @ i[3] + M[3] @ i[4] = N[0] @ o[1] + N[1] @ o[2] + N[2] @ o[3] + N[3] @ o[4]
	M[0] @ i[2] + M[1] @ i[3] + M[2] @ i[4] + M[3] @ i[5] = N[0] @ o[2] + N[1] @ o[3] + N[2] @ o[4] + N[3] @ o[5]
	M[0] @ i[3] + M[1] @ i[4] + M[2] @ i[5] + M[3] @ i[6] = N[0] @ o[3] + N[1] @ o[4] + N[2] @ o[5] + N[3] @ o[6]
	
	M[0] @ i[0] + M[1] @ i[1] + M[2] @ i[2] + M[3] @ i[3] = sum(Q[0, k] @ N[k]) @ o[0] + sum(Q[1, k] @ N[k]) @ o[1] + sum(Q[2, k] @ N[k]) @ o[2] + sum(Q[3, k] @ N[k]) @ o[3]
	M[0] @ i[1] + M[1] @ i[2] + M[2] @ i[3] + M[3] @ i[4] = sum(Q[0, k] @ N[k]) @ o[1] + sum(Q[1, k] @ N[k]) @ o[2] + sum(Q[2, k] @ N[k]) @ o[3] + sum(Q[3, k] @ N[k]) @ o[4]
	M[0] @ i[2] + M[1] @ i[3] + M[2] @ i[4] + M[3] @ i[5] = sum(Q[0, k] @ N[k]) @ o[2] + sum(Q[1, k] @ N[k]) @ o[3] + sum(Q[2, k] @ N[k]) @ o[4] + sum(Q[3, k] @ N[k]) @ o[5]
	M[0] @ i[3] + M[1] @ i[4] + M[2] @ i[5] + M[3] @ i[6] = sum(Q[0, k] @ N[k]) @ o[3] + sum(Q[1, k] @ N[k]) @ o[4] + sum(Q[2, k] @ N[k]) @ o[5] + sum(Q[3, k] @ N[k]) @ o[6]
	
	QQ[x] = sum(Q[x, z] @ N[z])
	
	1 = sum(Q[0, z] @ N[z])
	sum(Q[ya, z] @ N[z]) = sum(Q[yb, z] @ N[z]))
	
	QQ[0] = 1
	
	
	o = sum(F[x, y](i[x], i[y]))
	
	F[0, 0](i[0], i[0]) + F[0, 1](i[0], i[1]) + F[1, 0](i[1], i[0]) + F[1, 1](i[1], i[1])
	
	A @ F[x, y] @ (B[x], C[y])
	
	a*x + b*x**2 + c*x**4 + d*x**8
	
	a[0] * b[0] + a[1] * b[7]**128 + a[2] * b[6]**64
	
	
	
	F[0, 0] @ ii[0]
	F @ ii[1]
	F @ ii[2]
	F @ ii[3]
	
	
	on = f(in)
	in = g(on)
	
	
	on = f(i)
	
	
	
	
	
	o0 = G(i0, i1)
	i0 = Gi[i1](o0)

	

	
	i**2 = o
	
	f(x) = x**128
	
	i**256 = o**128
	i = o**128
	
	
	i**2 = o**128 * i
	



	
	
	m0 = o0 + N(o*) - M(m*)
	o0 = m0 - N(o*) + M(m*)

	m0 = i0 - O(i*) - P(m*)


	o0 = i0 - O(i*) - P(m*) - N(o*) + M(i* - O(i**) - P(m**))
	

	o[0] = A0(m[0]) + A1(m[-1]) + A2(m[-2]) + A3(m[-3]) + ... + B1(o[-1]) + B2(o[-2]) + B3(o[-3]) + ...
	m[0] = E0(o[0]) + E1(o[-1]) + E2(o[-2]) + E3(o[-3]) + ... + F1(m[-1]) + F2(m[-2]) + F3(m[-3]) + ...
	m[0] = C0(i[0]) + C1(i[-1]) + C2(i[-2]) + C3(i[-3]) + ... + D1(m[-1]) + D2(m[-2]) + D3(m[-3]) + ...
	
	A0(m[ 0]) = A0@C0(i[ 0]) + A0@C1(i[-1]) + A0@C2(i[-2]) + A0@C3(i[-3]) + ... + A0@D1(m[-1]) + A0@D2(m[-2]) + A0@D3(m[-3]) + ...
	A1(m[-1]) = A1@C0(i[-1]) + A1@C1(i[-2]) + A1@C2(i[-3]) + A1@C3(i[-4]) + ... + A1@D1(m[-2]) + A1@D2(m[-3]) + A1@D3(m[-4]) + ...
	A2(m[-2]) = A2@C0(i[-2]) + A2@C1(i[-3]) + A2@C2(i[-4]) + A2@C3(i[-5]) + ... + A2@D1(m[-3]) + A2@D2(m[-4]) + A2@D3(m[-5]) + ...
	A3(m[-3]) = A3@C0(i[-3]) + A3@C1(i[-4]) + A3@C2(i[-5]) + A3@C3(i[-6]) + ... + A3@D1(m[-4]) + A3@D2(m[-5]) + A3@D3(m[-6]) + ...
	


	o[0] = A0(m[0]) + A1(m[-1]) + A2(m[-2]) + A3(m[-3]) + ... + B1(o[-1]) + B2(o[-2]) + B3(o[-3]) + ...


	A(m) = B(o)
	C(i) = D(m)

	A@C(ii) = A@D(mm)
	A@D(mm) = B@D(oo)

	A@C(ii) = B@D(oo)


	B0@D0 B0@D1 B0@D2
	B1@D0 B1@D1 B1@D2
	B2@D0 B2@D1 B2@D2

	Ei0 = (Bi @ Dj)**-1


	o = A(m) + B(o*)
	m = C(i) + D(m*)
	A(m) = A@C(i) + A@D(m*)

	o = A@C(i) + A@D(m*) + B(o*)
	m = E(o) + F(m*)


	m[-1] = U(o[-1]) + E1(o[-2]) + E2(o[-3]) + E3(o[-4]) + ... + F1(m[-2]) + F2(m[-3]) + F3(m[-4]) + ...

	m[0] = U(o[0]) + E1(o[-1]) + E2(o[-2]) + E3(o[-3]) + ... + F1(m[-1]) + F2(m[-2]) + F3(m[-3]) + ...
	m[0] = U(o[0]) + E1(o[-1]) + E2(o[-2]) + E3(o[-3]) + ... + F1(m[-1]) + F2(m[-2]) + F3(m[-3]) + ...
	
	


	o[0] = M0(m[0]) + Mij(m[-i], m[-j]) + ... + Nij(o[-i], o[-j]) + ...
	m[0] = C0(i[0]) + Ck(i[-k]) + ... + Dk(m[-k]) + ...


	o[0] = M0(m[0]) + Mij((C0(i[-i]) + Ck(i[-i-k]) + ... + Dk(m[-i-k]) + ...), C0(i[-j]) + Ck(i[-j-k]) + ... + Dk(m[-j-k]) + ...) + ... 
+ Nij(o[-i], o[-j]) + ...

	Ck(i[-i-k]) * Cl(i[-j-l])



	E1
	E2 @ (D2*) @ N @ D1
	E1 @ D2
	
	y = d(x)
	
	if n == 12:
		return x
	else:
		return 0
	
	x x**2 x**3
	
	q00(x0, x0)
	q01(x0, x1)
	q10(x1, x0)
	q11(x1, x1)
	
	x0 := y0 + 1
	y0 := x0
	
	x1 := y1 + y0
	y1 := x1
	
	y01 := x0 * x1
	x2 := y2 + y01
	y2 := x2
	
	x3 := y3 + y2 * y01
	y3 := x3
	
	a3 * x**4 + a2 * x**2 + a1 * x + a0
	b3 * x**4 + b2 * x**2 + b1 * x + b0

	1	2	4	8	16	32	64	128	256
	3	6	12	24	48	
	
	x * y + x**2 * y
	
	'''


	'''
	def __matmul__(self, other):
		mid[i] = other.W * in_[i] + sum(other.A[m] * in_[m + i] for m in range(1, delay))
		out[0] = self.W * mid[0] + sum(self.A[n] * mid[n] for n in range(1, delay))

		out[0] = self.W * mid[0] + sum(self.A[n] * (other.W * in_[n] + sum(other.A[m] * in_[m + n] for m in range(1, delay))) for n in range(1, delay))

		out[0] = self.W * mid[0] + sum((self.A[n] * other.W * in_[n] + self.A[n] * sum(other.A[m] * in_[m + n] for m in range(1, delay))) for n in range(1, delay))
		out[0] = self.W * mid[0] + sum(self.A[n] * other.W * in_[n] for n in range(1, delay)) + sum(self.A[n] * sum(other.A[m] * in_[m + n] for m in range(1, delay)) for n in range(1, delay))

		AA[k] = sum(self.A[k] * other.A[k - l] for l in range(1, delay))

		out[0] = self.W * mid[0] + sum(self.A[n] * other.W * in_[n] for n in range(1, delay)) + sum(AA[n] * in_[n] for n in range(1, delay))

		out = (self.W @ other.W)(in_) + (self.A * other.W)(in_state) + (self.W * other.A)(in_state) + (self.A @ other.A)(in_state)

		W = self.W @ other.W
		A = self.A * other.W + self.W * other.A + self.A @ other.A
		B = self.B

		mid[i] = other.W * in_[i] + sum(other.A[m] * in_[m + i] for m in range(1, delay)) + sum(other.B[m] * mid[m + i] for m in range(1, delay))
		mid[i] = inverse.W * out[i] + sum(inverse.A[m] * out[m + i] for m in range(1, delay)) + sum(inverse.B[m] * mid[m + i] for m in range(1, delay))
		other.W * in_[i] + sum(other.A[m] * in_[m + i] for m in range(1, delay)) - inverse.W * out[i] - sum(inverse.A[m] * out[m + i] for m in range(1, delay)) = sum(inverse.B[m] * mid[m + i] for m in range(1, delay)) - sum(other.B[m] * mid[m + i] for m in range(1, delay))
		other.W * in_[i] + sum(other.A[m] * in_[m + i] for m in range(1, delay)) - inverse.W * out[i] - sum(inverse.A[m] * out[m + i] for m in range(1, delay)) = sum(inverse.B[m] * mid[m + i] - other.B[m] * mid[m + i] for m in range(1, delay))
		other.W * in_[i] + sum(other.A[m] * in_[m + i] for m in range(1, delay)) - inverse.W * out[i] - sum(inverse.A[m] * out[m + i] for m in range(1, delay)) = sum((inverse.B[m] - other.B[m]) * mid[m + i] for m in range(1, delay))


		W = self.W @ other.W + self.A @ (inverse.B - other.B).invert() @ other.W
		A = self.A * other.W + self.W * other.A + self.A @ other.A + self.A @ (self.B.invert() - other.B).invert() @ other.A
		B = self.B - self.A @ (self.B.invert() - other.B).invert() @ self.A.invert()

		self.A @ (inverse.B - other.B).invert() @ inverse.W = 0


		out[0] = self.W * mid[0]  + sum(self.A[n]  * mid[n] for n in range(1, delay))     + sum(self.B[n] * out[n] for n in range(1, delay))
	'''



if __debug__ and __name__ == '__main__':
	profile = False
	if profile:
		from pycallgraph2 import PyCallGraph
		from pycallgraph2.output.graphviz import GraphvizOutput
	
	from fields import Galois
	from random import randrange
	
	for F in Galois('Binary', 2, [1, 1]), Galois('F3', 3, [1, 0, 2, 1]), Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1]):
		print(F)
		
		def test():
			for n in range(5):
				a1 = LinearCircuit.random(randrange(1, 5), randrange(1, 5), dict, list, Linear, F, randrange)
				a2 = LinearCircuit.random(a1.output_size, a1.input_size, dict, list, Linear, F, randrange)
				b = LinearCircuit.random(randrange(1, 5), a1.output_size, dict, list, Linear, F, randrange)
				l = Linear.random(list, F, randrange)
				
				for m in range(5):
					x = Vector.random(a1.input_size, list, F, randrange)
					y = Vector.random(a1.input_size, list, F, randrange)
					
					assert len(a1(x)) == a1.output_size
					assert b(a1(x)) == (b @ a1)(x)
					assert b(a2(x)) == (b @ a2)(x)
					assert (b @ (a1 + a2))(x) == (b @ a1 + b @ a2)(x)
					assert a1(x + y) == a1(x) + a1(y)
					assert a1(x - y) == a1(x) - a1(y)
					assert (a1 + a2)(x) == a1(x) + a2(x)
					assert (a1 - a2)(x) == a1(x) - a2(x)
					
					assert (l * a1)(x) == Vector([l(_c) for _c in a1(x)])
					assert (a1 * l)(x) == a1(Vector([l(_c) for _c in x]))

		if profile:
			profiler = PyCallGraph(output=GraphvizOutput(output_file=f'linear_circuit_{F.__name__}.png'))
			profiler.start()
		
		test()
		
		if profile:
			profiler.done()
		
		
		if profile:
			profiler = PyCallGraph(output=GraphvizOutput(output_file=f'quadratic_circuit_{F.__name__}.png'))
			profiler.start()
		
		for n in range(5):
			a1 = QuadraticCircuit.random(randrange(2, 5), randrange(2, 5), dict, list, Quadratic, Linear, F, randrange)
			a2 = QuadraticCircuit.random(a1.output_size, a1.input_size, dict, list, Quadratic, Linear, F, randrange)
			b = LinearCircuit.random(randrange(2, 5), a1.output_size, dict, list, Linear, F, randrange)
			c = LinearCircuit.random(a1.input_size, randrange(2, 5), dict, list, Linear, F, randrange)
			l = Linear.random(list, F, randrange)
			#q = Quadratic.random(list, Linear, F, randrange)
			
			for m in range(5):
				x = Vector([F.random(randrange) for _n in range(a1.input_size)])
				y = Vector([F.random(randrange) for _n in range(c.input_size)])
				
				assert len(a1(x)) == a1.output_size
				assert (a1 + a2)(x) == a1(x) + a2(x)
				assert (a1 - a2)(x) == a1(x) - a2(x)
				assert b(a1(x)) == (b @ a1)(x)
				assert b(a2(x)) == (b @ a2)(x)
				assert (b @ (a1 + a2))(x) == (b @ a1 + b @ a2)(x)
				assert a1(c(y)) == (a1 @ c)(y)
				assert a2(c(y)) == (a2 @ c)(y)
				assert b(a1(c(y))) == (b @ a1 @ c)(y)
				assert b(a2(c(y))) == (b @ a2 @ c)(y)
				
				assert (l * a1)(x) == Vector([l(_c) for _c in a1(x)])
				assert (a1 * l)(x) == a1(Vector([l(_c) for _c in x]))				
		
		if profile:
			profiler.done()
	
	quit()
	
	'''
	def random_stream(n, size, Array, Field, randbelow):
		while n > 0:
			n -= 1
			yield Vector.random(size, Array, Field, randbelow)
	
	
	def ascending_stream(n, size, Array, Field):
		v = [0] * size
		while n > 0:
			n -= 1
			yield Vector(Array(map(Field, v)))
			
			carry = True
			for m in range(size):
				if carry:
					v[m] += 1
				
				if v[m] >= F.field_size:
					v[m] = 0
					carry = True
				else:
					carry = False
	
	
	print()
	a = Automaton.random_linear_linear(4, 3, 4, dict, list, Vector, LinearCircuit, Linear, F, randrange)
	for n, x in enumerate(a(random_stream(32, 3, list, F, randrange))):
		print(n, x)
	
	print()
	b = Automaton.random_linear_quadratic(4, 3, 4, dict, list, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
	for n, x in enumerate(b(random_stream(32, 3, list, F, randrange))):
		print(n, x)
	
	print()
	c = Automaton.random_quadratic_linear(4, 3, 4, dict, list, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
	for n, x in enumerate(c(random_stream(32, 3, list, F, randrange))):
		print(n, x)
	
	print()
	d = Automaton.random_quadratic_quadratic(4, 3, 4, dict, list, Vector, QuadraticCircuit, Quadratic, Linear, F, randrange)
	for n, x in enumerate(d(random_stream(32, 3, list, F, randrange))):
		print(n, x)
	
	'''
	
	class Loopback:
		def __init__(self):
			self.__value = None
			self.__stop = True
		
		def __iter__(self):
			return self
		
		def __next__(self):
			if self.__stop:
				raise StopIteration
			else:
				self.__stop = True
				return self.__value
		
		def push(self, value):
			self.__value = value
			self.__stop = False
	
	
	class Random:
		def __init__(self, n, out_size, Field, randrange):
			self.__out_size = out_size
			self.__Field = Field
			self.__randrange = randrange
			self.__n = n
		
		def __iter__(self):
			return self
		
		def __next__(self):
			if self.__n <= 0:
				raise StopIteration
			else:
				self.__n -= 1
				return Vector.random(self.__out_size, list, self.__Field, self.__randrange)	
	
	
	F = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	out_size = 2
	#a = MemoryAutomaton.random_linear(out_size, out_size * 4, dict, list, Vector, LinearCircuit, Linear, F, randrange)
	a = MemoryAutomaton.random_quadratic(out_size, out_size * 4, dict, list, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
	b = MemoryAutomaton.random_quadratic(out_size, out_size * 4, dict, list, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
	
	print()
	loopback1 = Loopback()
	loopback2 = Loopback()
	#loopback.push(Vector.random(out_size, list, F, randrange))
	
	if profile:
		profiler = PyCallGraph(output=GraphvizOutput(output_file='quadratic_automaton_memory.png'))
		profiler.start()
	
	z = Vector.random(out_size, list, F, randrange)
	loopback1.push(z)
	loopback2.push(z)
	for n, x, y in enumerate(zip(a(b(loopback1)), (a @ b)(loopback2))):
		print(n, x, y)
		if n < 4:
			z = Vector.random(out_size, list, F, randrange)
			loopback1.push(z)
			loopback2.push(z)
	
	if profile:
		profiler.done()



