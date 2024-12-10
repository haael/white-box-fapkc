#!/usr/bin/python3


"Computational 'machines', i.e. circuits and automata that allow for fast calculations of large amounts of elements of finite fields."


__all__ = 'LinearCircuit', 'QuadraticCircuit', 'Automaton'


from itertools import product, chain
from collections import defaultdict

from vectors import *
from operations import *
from polynomials import *

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
			if not isinstance(output_size, int):
				raise ValueError
			self.output_size = output_size
		else:
			self.output_size = len(set(_a for (_a, _b) in functions.keys()))
		
		if input_size is not None:
			if not isinstance(input_size, int):
				raise ValueError
			self.input_size = input_size
		else:
			self.input_size = len(set(_b for (_a, _b) in functions.keys()))
		
		self.__functions = functions
	
	def __getnewargs__(self):
		return self.__functions, self.output_size, self.input_size
	
	def serialize(self):
		try:
			return self.__functions.serialize()
		except AttributeError:
			return chain.from_iterable(_v.serialize() for _v in self.__functions)
	
	@classmethod
	def deserialize(cls, output_size, input_size, Table, Array, Linear, Field, data):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), Linear.deserialize(Array, Field, data)) for (_m, _n) in product(range(output_size), range(input_size))), [output_size, input_size], [Field.field_power, None], [Linear, Field], Array=Array))
	
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
		"Difference of two linear circuits: `(a - b)(x) = a(x) - b(x)`."
		
		if self.input_size != other.input_size:
			raise ValueError("Input sizes of linear circuits to subtract should be the same.")
		
		if self.output_size != other.output_size:
			raise ValueError("Output sizes of linear circuits to subtract should be the same.")
		
		try:
			return self.__class__(self.Table((((m, n), self[m, n] - other[m, n]) for n in range(self.input_size) for m in range(self.output_size)), [self.output_size, self.input_size], [self.Field.field_power, None], [self.Linear, self.Field], Array=self.Array))
		except TypeError:
			return NotImplemented
	
	def __neg__(self):
		"Linear circuit returning negated result: `(-a)(x) = -a(x)`."
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
		"Composition of linear circuit with linear operation (right hand): `(a * l)(x) = a([l(_x) for _x in x])`."
		return self.__class__(self.Table((((m, n), (self[m, n] @ other)) for n in range(self.input_size) for m in range(self.output_size)), [self.output_size, self.input_size], [self.Field.field_power, None], [self.Linear, self.Field], Array=self.Array))
	
	def __rmul__(self, other):
		"Composition of linear circuit with linear operation (left hand): `(l * a)(x) = [l(_x) for _x in a(x)]`."
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
	
	def __getnewargs__(self):
		return self.__functions, self.output_size, self.input_size
	
	def serialize(self):
		try:
			return self.__functions.serialize()
		except AttributeError:
			return chain.from_iterable(_v.serialize() for _v in self.__functions)
	
	@classmethod
	def deserialize(cls, output_size, input_size, Table, Array, Quadratic, Linear, Field, data):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n, _o), Quadratic.deserialize(Array, Linear, Field, data)) for (_m, _n, _o) in product(range(output_size), range(input_size), range(input_size))), [output_size, input_size, input_size], [Field.field_power, Field.field_power, None], [Quadratic, Linear, Field], Array=Array))
	
	def __getitem__(self, index):
		try:
			m, n, o = index
		except ValueError:
			raise TypeError(f"QuadraticCircuit.__getitem__ expects 3 numeric indices. Got: {index}")
		
		return self.__functions[m, n, o]
	
	def __call__(self, args):
		return args.__class__(args.Array((self.Field.sum(self[m, k, l](args[k], args[l]) for (k, l) in product(range(self.input_size), range(self.input_size))) for m in range(self.output_size)), [None], [self.Field]))
	
	def __add__(self, other):
		"Sum of two quadratic circuits: `(a + b)(x) = a(x) + b(x)`."
		if self.input_size != other.input_size: raise ValueError(f"Input sizes of quadratic circuits to add should be the same (got {self.input_size} vs. {other.input_size}).")
		if self.output_size != other.output_size: raise ValueError(f"Output sizes of quadratic circuits to add should be the same (got {self.output_size} vs. {other.output_size}).")
		return self.__class__(self.Table((((m, n, o), self[m, n, o] + other[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size))), [self.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __sub__(self, other):
		"Difference of two quadratic circuits: `(a - b)(x) = a(x) - b(x)`."
		if self.input_size != other.input_size: raise ValueError(f"Input sizes of quadratic circuits to subtract should be the same (got {self.input_size} vs. {other.input_size}).")
		if self.output_size != other.output_size: raise ValueError(f"Output sizes of quadratic circuits to subtract should be the same (got {self.output_size} vs. {other.output_size}).")
		return self.__class__(self.Table((((m, n, o), self[m, n, o] - other[m, n, o]) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size))), [self.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __neg__(self):
		"Quadratic circuit returning negated result: `(-a)(x) = -a(x)`."
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
		"Composition of quadratic circuit with linear operation (right hand): `(a * l)(x) = a([l(_x) for _x in x])`."
		return self.__class__(self.Table((((m, n, o), self[m, n, o] @ (other, other)) for (m, n, o) in product(range(self.output_size), range(self.input_size), range(self.input_size))), [self.output_size, self.input_size, self.input_size], [self.Field.field_power, self.Field.field_power, None], [self.Quadratic, self.Linear, self.Field], Array=self.Array))
	
	def __rmul__(self, other):
		"Composition of quadratic circuit with linear operation (left hand): `(l * a)(x) = [l(_x) for _x in a(x)]`."
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
	
	def serialize(self):
		yield from self.out_transition.serialize()
		yield from self.state_transition.serialize()
		yield from self.init_state.serialize()
	
	@classmethod
	def deserialize_linear_linear(cls, output_size, input_size, state_size, Dictionary, Array, Vector, LinearCircuit, Linear, Field, data):
		out_transition = LinearCircuit.deserialize(output_size, input_size + state_size, Dictionary, Array, Linear, Field, data)
		state_transition = LinearCircuit.deserialize(state_size, input_size + state_size, Dictionary, Array, Linear, Field, data)
		init_state = Vector.deserialize(state_size, Array, Field, data)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def deserialize_linear_quadratic(cls, output_size, input_size, state_size, Dictionary, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, data):
		out_transition = LinearCircuit.deserialize(output_size, input_size + state_size, Dictionary, Array, Linear, Field, data)
		state_transition = QuadraticCircuit.deserialize(state_size, input_size + state_size, Dictionary, Array, Quadratic, Linear, Field, data)
		init_state = Vector.deserialize(state_size, Array, Field, data)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def deserialize_quadratic_linear(cls, output_size, input_size, state_size, Dictionary, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, data):
		out_transition = QuadraticCircuit.deserialize(output_size, input_size + state_size, Dictionary, Array, Quadratic, Linear, Field, data)
		state_transition = LinearCircuit.deserialize(state_size, input_size + state_size, Dictionary, Array, Linear, Field, data)
		init_state = Vector.deserialize(state_size, Array, Field, data)
		return cls(out_transition, state_transition, init_state)
	
	@classmethod
	def deserialize_quadratic_quadratic(cls, output_size, input_size, state_size, Dictionary, Array, Vector, QuadraticCircuit, Quadratic, Linear, Field, data):
		out_transition = QuadraticCircuit.deserialize(output_size, input_size + state_size, Dictionary, Array, Quadratic, Linear, Field, data)
		state_transition = QuadraticCircuit.deserialize(state_size, input_size + state_size, Dictionary, Array, Quadratic, Linear, Field, data)
		init_state = Vector.deserialize(state_size, Array, Field, data)
		return cls(out_transition, state_transition, init_state)
	
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
		
		for n in range(2):
			a1 = QuadraticCircuit.random(randrange(2, 5), randrange(2, 5), dict, list, Quadratic, Linear, F, randrange)
			a2 = QuadraticCircuit.random(a1.output_size, a1.input_size, dict, list, Quadratic, Linear, F, randrange)
			b = LinearCircuit.random(randrange(2, 5), a1.output_size, dict, list, Linear, F, randrange)
			c = LinearCircuit.random(a1.input_size, randrange(2, 5), dict, list, Linear, F, randrange)
			l = Linear.random(list, F, randrange)
			#q = Quadratic.random(list, Linear, F, randrange)
			
			for m in range(2):
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

