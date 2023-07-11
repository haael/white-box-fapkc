#!/usr/bin/python3


from itertools import product
from collections import defaultdict

from linear import *
from utils import superscript, cached


class LinearCircuit:
	@property
	def Field(self):
		return self[0, 0].Field
	
	@property
	def Linear(self):
		return self[0, 0].Linear
	
	@classmethod
	def random(cls, output_size, input_size, Linear, Field, randbelow):
		return cls(((_m, _n), Linear.random(Field, randbelow)) for (_m, _n) in product(range(output_size), range(input_size)))
	
	def __init__(self, functions):
		self.l_functions = dict(functions)
		self.input_size = max(_b for (_a, _b) in self.l_functions.keys()) + 1
		self.output_size = max(_a for (_a, _b) in self.l_functions.keys()) + 1
	
	def __getitem__(self, index):
		try:
			m, n = index
		except ValueError:
			raise TypeError("LinearCircuit.__getitem__ expects 2 numeric indices.")
		
		return self.l_functions[m, n]
	
	def __call__(self, args):
		if len(args) != self.input_size:
			raise ValueError("Input size does not match circuit requirements.")
		
		return args.__class__(sum((self[m, k](args[k]) for k in range(self.input_size)), self.Field(0)) for m in range(self.output_size))
	
	def __add__(self, other):
		"Sum of two linear circuits: `(a + b)(x) = a(x) + b(x)`."
		
		if self.input_size != other.input_size:
			raise ValueError("Input sizes of linear circuits to add should be the same.")
		
		if self.output_size != other.output_size:
			raise ValueError("Output sizes of linear circuits to add should be the same.")
		
		try:
			return self.__class__(((m, n), self[m, n] + other[m, n]) for n in range(self.input_size) for m in range(self.output_size))
		except TypeError:
			return NotImplemented
	
	def __sub__(self, other):
		"Difference of two linear circuits: `(a - b)(x) = a(x) - b(x)`"
		
		if self.input_size != other.input_size:
			raise ValueError("Input sizes of linear circuits to subtract should be the same.")
		
		if self.output_size != other.output_size:
			raise ValueError("Output sizes of linear circuits to subtract should be the same.")
		
		try:
			return self.__class__(((m, n), self[m, n] - other[m, n]) for n in range(self.input_size) for m in range(self.output_size))
		except TypeError:
			return NotImplemented
	
	def __neg__(self):
		try:
			return self.__class__(((m, n), -self[m, n]) for n in range(self.input_size) for m in range(self.output_size))
		except TypeError:
			return NotImplemented
	
	def __matmul__(self, other):
		"Composition of two linear circuits: `(a @ b)(x) = a(b(x))`."
		
		if self.input_size != other.output_size:
			raise ValueError(f"Input size of the left circuit (got {self.input_size}) should match output size of the right circuit (got {other.output_size}).")
		
		try:
			return self.__class__(((m, n), sum((self[m, k] @ other[k, n] for k in range(self.input_size)), self.Linear.zero(self.Field))) for n in range(other.input_size) for m in range(self.output_size))
		except TypeError:
			return NotImplemented
	
	def print_matrix(self):
		for m in range(self.output_size):
			for k in range(self.Field.field_power):
				r = []
				for n in range(self.input_size):
					r.append(self[m, n].linear_coefficient(k))
				print(" ".join([str(_r) for _r in r]))
			print()


class QuadraticCircuit:
	@property
	def Field(self):
		return self[0, 0, 0].Field	
	
	@property
	def Linear(self):
		return self[0, 0, 0].Linear
	
	@property
	def Quadratic(self):
		return self[0, 0, 0].Quadratic
	
	@classmethod
	def random(cls, output_size, input_size, Quadratic, Linear, Field, randbelow):
		return cls(((_m, _n, _o), Quadratic.random(Linear, Field, randbelow)) for (_m, _n, _o) in product(range(output_size), range(input_size), range(input_size)))
	
	def __init__(self, functions):
		self.q_functions = dict(functions)		
		self.input_size = len(set(_b for (_a, _b, _c) in self.q_functions.keys()))
		self.output_size = len(set(_a for (_a, _b, _c) in self.q_functions.keys()))
	
	def __getitem__(self, index):
		try:
			m, n, o = index
		except ValueError:
			raise TypeError("QuadraticCircuit.__getitem__ expects 3 numeric indices.")
		
		return self.q_functions[m, n, o]
	
	def __call__(self, args):
		return args.__class__(sum((self[m, k, l](args[k], args[l]) for k in range(self.input_size) for l in range(self.input_size)), self.Field(0)) for m in range(self.output_size))
	
	def __add__(self, other):
		"Sum of two quadratic circuits: `(a + b)(x) = a(x) + b(x)`."
		if self.input_size != other.input_size: raise ValueError(f"Input sizes of quadratic circuits to add should be the same (got {self.input_size} vs. {other.input_size}).")
		if self.output_size != other.output_size: raise ValueError(f"Output sizes of quadratic circuits to add should be the same (got {self.output_size} vs. {other.output_size}).")
		return self.__class__(((m, n, o), self[m, n, o] + other[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size)))
	
	def __sub__(self, other):
		"Difference of two quadratic circuits: `(a - b)(x) = a(x) - b(x)`"
		if self.input_size != other.input_size: raise ValueError(f"Input sizes of quadratic circuits to subtract should be the same (got {self.input_size} vs. {other.input_size}).")
		if self.output_size != other.output_size: raise ValueError(f"Output sizes of quadratic circuits to subtract should be the same (got {self.output_size} vs. {other.output_size}).")
		return self.__class__(((m, n, o), self[m, n, o] - other[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size)))
	
	def __neg__(self):
		return self.__class__(((m, n, o), -self[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size)))
	
	def __matmul__(self, other):
		"Composition of a quadratic circuit with a linear one. Linear is applied first, quadratic next: `(q @ l)(x) = q(l(x))`. Result is a quadratic circuit."
		if self.input_size != other.output_size: raise ValueError(f"Input size of left automaton (got {self.input_size}) must match output size of the right automaton (got {other.output_size}).")		
		return self.__class__(((q, i, j), sum((self[q, o, p] @ (other[o, i], other[p, j]) for o in range(self.input_size) for p in range(self.input_size)), self.Quadratic.zero(self.Linear, self.Field))) for q in range(self.output_size) for i in range(other.input_size) for j in range(other.input_size))
	
	def __rmatmul__(self, other):
		"Composition of a linear circuit with a quadratic one. Quadratic is applied first, linear next: `(l @ q)(x) = l(q(x))`. Result is a quadratic circuit."
		if self.output_size != other.input_size: raise ValueError(f"Output size of right automaton (got {self.output_size}) must match input size of the left automaton (got {other.input_size}).")
		return self.__class__(((a, c, d), sum((other[a, b] @ self[b, c, d] for b in range(self.output_size)), self.Quadratic.zero(self.Linear, self.Field))) for a in range(other.output_size) for c in range(self.input_size) for d in range(self.input_size))


class Automaton:
	@classmethod
	def random_linear_linear(cls, output_size, input_size, state_size, Vector, LinearCircuit, Linear, Field, randbelow):
		out_transition = LinearCircuit.random(output_size, input_size + state_size, Linear, Field, randbelow)
		state_transition = LinearCircuit.random(state_size, input_size + state_size, Linear, Field, randbelow)
		init_state = Vector.random(state_size, Field, randbelow)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def random_linear_quadratic(cls, output_size, input_size, state_size, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randbelow):
		out_transition = LinearCircuit.random(output_size, input_size + state_size, Linear, Field, randbelow)
		state_transition = QuadraticCircuit.random(state_size, input_size + state_size, Quadratic, Linear, Field, randbelow)
		init_state = Vector.random(state_size, Field, randbelow)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def random_quadratic_linear(cls, output_size, input_size, state_size, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randbelow):
		out_transition = QuadraticCircuit.random(output_size, input_size + state_size, Quadratic, Linear, Field, randbelow)
		state_transition = LinearCircuit.random(state_size, input_size + state_size, Linear, Field, randbelow)
		init_state = Vector.random(state_size, Field, randbelow)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def random_quadratic_quadratic(cls, output_size, input_size, state_size, Vector, QuadraticCircuit, Quadratic, Linear, Field, randbelow):
		out_transition = QuadraticCircuit.random(output_size, input_size + state_size, Quadratic, Linear, Field, randbelow)
		state_transition = QuadraticCircuit.random(state_size, input_size + state_size, Quadratic, Linear, Field, randbelow)
		init_state = Vector.random(state_size, Field, randbelow)
		return cls(out_transition, state_transition, init_state)
	
	def __init__(self, out_transition, state_transition, init_state):
		self.out_transition = out_transition
		self.state_transition = state_transition
		self.init_state = init_state
	
	def __call__(self, stream):
		state = self.init_state
		for word in stream:
			yield self.out_transition(word | state)
			state = self.state_transition(word | state)
	
	def __matmul__(self, other):
		out_transition = self.out_transition @ (other.out_transition | shift_state)
		state_transition = (self.state_transition @ other.out_transition) | other.state_transition
		init_state = other.state_transition | self.state_transition
		return self.__class__(out_transition, state_transition, init_state)


if __debug__ and __name__ == '__main__':
	#from pycallgraph2 import PyCallGraph
	#from pycallgraph2.output.graphviz import GraphvizOutput
	from fields import Galois
	from random import randrange
	
	F = Galois('F', 3, [1, 0, 2, 1])
	#F = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	
	
	#profiler = PyCallGraph(output=GraphvizOutput(output_file='linear_circuit.png'))
	#profiler.start()
	
	for n in range(2):
		a1 = LinearCircuit.random(randrange(1, 10), randrange(1, 10), Linear, F, randrange)
		a2 = LinearCircuit.random(a1.output_size, a1.input_size, Linear, F, randrange)
		b = LinearCircuit.random(randrange(1, 10), a1.output_size, Linear, F, randrange)
		
		for m in range(6):
			x = Vector.random(a1.input_size, F, randrange)
			y = Vector.random(a1.input_size, F, randrange)
			
			assert len(a1(x)) == a1.output_size
			assert b(a1(x)) == (b @ a1)(x)
			assert b(a2(x)) == (b @ a2)(x)
			assert (b @ (a1 + a2))(x) == (b @ a1 + b @ a2)(x)
			assert a1(x + y) == a1(x) + a1(y)
			assert a1(x - y) == a1(x) - a1(y)
			assert (a1 + a2)(x) == a1(x) + a2(x)
			assert (a1 - a2)(x) == a1(x) - a2(x)
		
		#a1.print_matrix()
		#print()
	
	#profiler.done()
	
	
	#profiler = PyCallGraph(output=GraphvizOutput(output_file='quadratic_circuit.png'))
	#profiler.start()
	
	for n in range(2):		
		a1 = QuadraticCircuit.random(randrange(2, 10), randrange(2, 10), Quadratic, Linear, F, randrange)
		a2 = QuadraticCircuit.random(a1.output_size, a1.input_size, Quadratic, Linear, F, randrange)
		b = LinearCircuit.random(randrange(2, 10), a1.output_size, Linear, F, randrange)
		c = LinearCircuit.random(a1.input_size, randrange(2, 10), Linear, F, randrange)
		
		for m in range(6):
			x = Vector(F.random(randrange) for _n in range(a1.input_size))
			y = Vector(F.random(randrange) for _n in range(c.input_size))
			
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
		
		#a1.print_matrix()
		#print()
	
	#profiler.done()
	
	
	def random_stream(n, size, F, randbelow):
		while n > 0:
			n -= 1
			yield Vector.random(size, F, randbelow)
	
	
	def ascending_stream(n, size, F):
		v = [0] * size
		while n > 0:
			n -= 1
			yield Vector(map(F, v))
			
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
	a = Automaton.random_linear_linear(4, 3, 4, Vector, LinearCircuit, Linear, F, randrange)
	for x in enumerate(a(random_stream(512, 3, F, randrange))):
		print(n, x)
	
	print()
	b = Automaton.random_linear_quadratic(4, 3, 4, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
	for x in enumerate(b(random_stream(512, 3, F, randrange))):
		print(n, x)
	
	print()
	c = Automaton.random_quadratic_linear(4, 3, 4, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
	for x in enumerate(c(random_stream(512, 3, F, randrange))):
		print(n, x)
	
	print()
	d = Automaton.random_quadratic_quadratic(4, 3, 4, Vector, QuadraticCircuit, Quadratic, Linear, F, randrange)
	for x in enumerate(d(random_stream(512, 3, F, randrange))):
		print(n, x)
	
	
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
	
	
	a = Automaton.random_quadratic_quadratic(4, 4, 0, Vector, QuadraticCircuit, Quadratic, Linear, F, randrange)
	
	
	loopback = Loopback()
	loopback.push(Vector.random(4, F, randrange))
	for n, x in enumerate(a(loopback)):
		print(x)
		if n < 50:
			loopback.push(x)




