#!/usr/bin/python3


"This module provides classes `Array` (list-like) and `Table` (dict-like) that can be used to implement different memory layout for circuits and finite automata."


__all__ = 'Array', 'Table'


from itertools import chain, product
from utils import cached


class Array:
	"One-dimensional array of elements that fit in 1 byte. Supports non-scalar subelements of uniform size, as long as they accept Array in the constructor."
	
	StorageType = bytearray
	Storage = bytearray
	cast = int
	
	@classmethod
	@property
	def Array(cls):
		return cls
	
	def __init__(self, values, sizes=None, types=None, start=None, stop=None, step=None):
		try:
			if sizes is not None:
				self.__sizes = sizes
			else:
				self.__sizes = values.__sizes
			
			if types is not None:
				self.__types = types
			else:
				self.__types = values.__types
			
			self.__storage = values.__storage
			
			if start is not None:
				self.__start = start
			else:
				self.__start = values.__start
			
			if stop is not None:
				self.__stop = stop
			else:
				self.__stop = values.__stop
			
			if step is not None:
				self.__step = step
			else:
				self.__step = values.__step
		
		except AttributeError as error:
			#print("array init", error)
			
			if sizes is not None:
				self.__sizes = sizes
			else:
				raise TypeError("`sizes` argument required.")
			
			if types is not None:
				self.__types = types
			else:
				raise TypeError("`types` argument required.")
			
			if isinstance(values, self.StorageType):
				self.__storage = values
			elif self.__sizes[0] is None:
				#print("array copy 1", type(values), self.StorageType)
				self.__storage = self.__class__.Storage(self.__class__.cast(_value) for _value in values)
			else:
				#print("array copy 2", type(values), self.StorageType)
				self.__storage = self.__class__.Storage(chain.from_iterable(_value.serialize() for _value in values))	
			
			if start is not None:
				self.__start = start
			else:
				self.__start = 0
			
			if stop is not None:
				self.__stop = stop
			else:
				self.__stop = len(self.__storage)
			
			if step is not None:
				self.__step = step
			else:
				self.__step = 1
		
		if self.__step != 1:
			#print(self.__step)
			raise NotImplementedError
		
		#assert len(self) == len(self.serialize())
		assert len(self.__storage) % self.__element_size() == 0
		assert (self.__stop - self.__start) % self.__element_size() == 0
	
	@cached
	def __element_size(self):
		size = 1
		for s in self.__sizes:
			if s is not None:
				size *= s
		return size
	
	def __eq__(self, other):
		try:
			return self.serialize() == other.serialize() # FIXME
		except AttributeError:
			return NotImplemented
	
	def __len__(self):
		return (self.__stop - self.__start) // self.__element_size()
	
	def serialize(self):
		return memoryview(self.__storage)[self.__start:self.__stop]
	
	def __getitem__(self, index):
		if index is Ellipsis or (hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step')):
			if index is Ellipsis:
				start = 0
				stop = len(self)
				step = 1
			else:
				start = index.start
				if start is None:
					start = 0
				
				stop = index.stop
				if stop is None:
					stop = len(self)
				
				step = index.step
				if step is None:
					step = 1
			
			return self.__class__(self, start=self.__start + self.__element_size() * start, stop=self.__start + self.__element_size() * stop, step=step)
		
		else:
			if self.__sizes[0] is None:
				if index < 0:
					if self.__step != 1:
						raise NotImplementedError
					index = self.__stop - self.__start + index
					if index < 0:
						raise IndexError(f"Index too low ({str(index)}).")
				if self.__start + index >= self.__stop:
					raise IndexError(f"Index {index} exceeds array length {self.__stop - self.__start}")
				return self.__types[0](self.__storage[self.__start + index * self.__step])
			else:
				return self.__types[0](self.__class__(self, start=self.__start + self.__element_size() * self.__step * index, stop=self.__start + self.__element_size() * self.__step * (index + 1), step=1, sizes=self.__sizes[1:], types=self.__types[1:]))
	
	def __setitem__(self, index, value):
		if index is Ellipsis or (hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step')):
			if index is Ellipsis:
				start = 0
				stop = len(self)
				step = 1
			else:
				start = index.start
				if start is None:
					start = 0
				
				stop = index.stop
				if stop is None:
					stop = len(self)
				
				step = index.step
				if step is None:
					step = 1
			
			for index, v in zip(range(start, stop, step), value):
				self[index] = v
		
		else:
			if self.__sizes[0] is None:
				if index < 0:
					if self.__step != 1:
						raise NotImplementedError
					index = self.__stop - self.__start + index
					if index < 0:
						raise IndexError("Index too low.")
				if self.__start + index >= self.__stop:
					raise IndexError(f"Index {index} exceeds array length {self.__stop - self.__start}")
				
				self.__storage[self.__start + index * self.__step] = self.__class__.cast(value)
			else:
				for n, v in enumerate(value):
					self[index][n] = v


class Table:
	"Multi-dimensional table of elements that fit in 1 byte. Supports non-scalar subelements of uniform size, as long as they accept Table in the constructor."
	
	StorageType = bytearray
	Storage = bytearray
	cast = int
	
	@classmethod
	@property
	def Table(cls):
		return cls
	
	@classmethod
	def __flatten_tuple(cls, t):
		if not isinstance(t, tuple): return (t,)
		a, b = t
		a = cls.__flatten_tuple(a)
		b = cls.__flatten_tuple(b)
		return a + b
	
	def __init__(self, items, ksize=None, sizes=None, types=None, start=None, stop=None, Array=None):
		try:
			self.__storage = items.__storage
			
			if ksize is not None:
				self.__ksize = ksize
			else:
				self.__ksize = items.__ksize
			
			if sizes is not None:
				self.__sizes = sizes
			else:
				self.__sizes = items.__sizes
			
			if types is not None:
				self.__types = types
			else:
				self.__types = items.__types
			
			if start is not None:
				self.__start = start
			else:
				self.__start = items.__start
			
			if stop is not None:
				self.__stop = stop
			else:
				self.__stop = items.__stop
			
			if Array is not None:
				self.Array = Array
			else:
				self.Array = items.Array
		
		except AttributeError:
			if sizes is not None:
				self.__sizes = sizes
			else:
				raise TypeError("`sizes` argument required.")
			
			if types is not None:
				self.__types = types
			else:
				raise TypeError("`types` argument required.")
			
			items = dict(items)
			
			if ksize is None:
				keys = frozenset(items.keys())
				key = next(iter(keys))
				ksize = [max(_k[_n] for _k in keys) + 1 for _n in range(len(key))]
			
			self.__ksize = ksize
			
			if isinstance(items, self.StorageType):
				self.__storage = items
			else:
				indices = range(ksize[0])
				for s in ksize[1:]:
					indices = product(indices, range(s))
				
				def values():
					for index in indices:
						index = self.__flatten_tuple(index)
						offset = 0
						for i, s in zip(index, ksize):
							offset *= s
							offset += i
						
						if hasattr(items[index], 'serialize'):
							yield from items[index].serialize()
						else:
							yield self.__class__.cast(items[index])
				
				#print("table copy")
				self.__storage = self.__class__.Storage(values())
			
			if start is not None:
				self.__start = start
			else:
				self.__start = 0
			
			if stop is not None:
				self.__stop = stop
			else:
				self.__stop = len(self.__storage)
			
			self.Array = Array
	
	def serialize(self):
		return memoryview(self.__storage)[self.__start:self.__stop]
	
	def keys(self):
		indices = range(self.__ksize[0])
		for s in self.__ksize[1:]:
			indices = product(indices, range(s))
		for index in indices:
			yield self.__flatten_tuple(index)
	
	def values(self):
		for index in self.keys():
			yield self[index]
	
	def items(self):
		for index in self.keys():
			yield index, self[index]
	
	def __len__(self):
		size = 1
		for s in self.__ksize:
			if s is not None:
				size *= s
		return size
	
	def __getitem__(self, index):
		if len(index) != len(self.__ksize):
			raise KeyError(f"Expected {len(self.__ksize)}-tuple.")
		
		offset = 0
		for i, s in zip(index, self.__ksize):
			if not 0 <= i < s:
				raise KeyError(f"Index {tuple(index)} out of bounds: {tuple(self.__ksize)}")
			offset *= s
			offset += i
		
		size = 1
		for s in self.__sizes:
			if s is None:
				pass
			elif not isinstance(s, tuple):
				size *= s
			else:
				for ss in s:
					size *= ss
		
		if self.__sizes[0] is None:
			return self.__types[0](self.__storage[offset])
		elif not isinstance(self.__sizes[0], tuple):
			#print("table getitem create array")
			return self.__types[0](self.Array(self.__storage, sizes=self.__sizes[1:], types=self.__types[1:], start=offset * size, stop=(offset + 1) * size))
		else:
			return self.__types[0](self.__class__(self, ksize=self.__sizes[0], sizes=self.__sizes[1:], types=self.__types[1:], start=offset * size, stop=(offset + 1) * size, Array=self.Array))


if __debug__ and __name__ == '__main__':
	from pycallgraph2 import PyCallGraph
	from pycallgraph2.output.graphviz import GraphvizOutput
	
	from random import randrange
	from fields import Galois
	from linear import *
	from machines import *
	
	from numpy import array, uint8, fromiter, bitwise_xor
	
	PyArray = Array
	PyTable = Table
	
	class NpArray(PyArray):
		StorageType = type(array([0], dtype=uint8))
		Storage = lambda x: fromiter(x, dtype=uint8)
		
		def __eq__(self, other):
			try:
				return (self.serialize() == other.serialize()).all()
			except AttributeError:
				return NotImplemented
	
	class NpTable(PyTable):
		StorageType = type(array([0], dtype=uint8))
		Storage = lambda x: fromiter(x, dtype=uint8)
		
		def __eq__(self, other):
			try:
				return (self.serialize() == other.serialize()).all()
			except AttributeError:
				return NotImplemented
	
	for m_impl in ('py', 'np', 'np+'):
		if m_impl == 'py':
			Array = PyArray
			Table = PyTable
		elif m_impl in ('np', 'np+'):
			Array = NpArray
			Table = NpTable
		
		for Field in (Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1]),):   #, Galois('F3', 3, [1, 0, 2, 1]), Galois('Binary', 2, [1, 1]):
			if m_impl == 'np+' and Field.__name__ == 'Rijndael':
				class Field(Field):
					@classmethod
					def sum(cls, values):
						return cls(bitwise_xor.reduce(array(fromiter(values, dtype=uint8), dtype=uint8)))
				Field.__name__ = 'Rijndael'
			
			if Field.__name__ == 'Binary':
				F = lambda x: Field(x % 2)
			else:
				F = Field
			
			a1 = Array([F(0), F(1), F(2), F(3)], [None], [F])
			
			a1s = a1[1:4]
			assert a1s[0] == F(1)
			assert a1s[2] == a1[3]
			
			a2 = Array([F(4), F(5), F(6), F(7)], [None], [F])
			a3 = Array([F(8), F(9), F(10), F(11)], [None], [F])
			
			an = Array([a1, a2, a3], [4, None], [Array, F])
			
			assert an[0][0] == F(0)
			assert an[0][1] == F(1)
			assert an[1][0] == F(4)
			assert an[2][3] == F(11)
			assert isinstance(a2[0], F)
			
			ans = an[1:3]
			assert ans[0] == an[1]
			assert ans[1] == an[2]
			assert ans[2] == an[3]
			
			an1 = Array([a1, a2, a3], [4, None], [Array, F])
			print("storage", type(an1._Array__storage), repr(an1._Array__storage))
			an2 = Array([a3, a1, a2], [4, None], [Array, F])
			
			ann = Array([an1, an2], [3, 4, None], [Array, Array, F])
			
			assert ann[1][0][2] == F(10)
			
			ann[1][0][2] = F(11)
			assert ann[1][0][2] == F(11)
			
			ann[1][1] = [F(1), F(2), F(3), F(4)]
			assert ann[1][1][2] == F(3)
			
			ann[1][1][:] = [F(5), F(6), F(7), F(8)]
			assert ann[1][1][2] == F(7)
			
			ann[1][1][...] = [F(9), F(10), F(11), F(12)]
			assert ann[1][1][2] == F(11)
			
			ann[...] = [[[F(m * n + k) for n in range(4)] for m in range(3)] for k in range(2)]
			assert ann[0][2][3] == F(6)
			assert ann[0][1][2] == F(2)
			assert ann[1][2][3] == F(7)
			assert ann[1][1][2] == F(3)
			
			l1 = Linear(Array([F(_n + 1) for _n in range(F.field_power)], [None], [F]))
			print("l1", l1._Linear__f)
			l2 = Linear.random(Array, F, randrange)
			print(l1, l2, l1 + l2)
			
			q1 = Quadratic(Array([Linear(Array([F((_n + _m * F.field_power + 1)  % F.field_size) for _n in range(F.field_power)], [None], [F])) for _m in range(F.field_power)], [F.field_power, None], [Linear, F]))
			q2 = Quadratic.random(Array, Linear, F, randrange)
			print(q1, q2, q1 + q2)
			
			v1 = Vector(Array([F(1), F(2), F(3), F(4)], [None], [F]))
			v2 = Vector.random(4, Array, F, randrange)
			print(v1, v2, v1 + v2)
			
			t1 = Table([((0, 0), F(0)), ((0, 1), F(1)), ((0, 2), F(2)), ((0, 3), F(3)), ((1, 0), F(4)), ((1, 1), F(5)), ((1, 2), F(6)), ((1, 3), F(7)), ((2, 0), F(8)), ((2, 1), F(9)), ((2, 2), F(10)), ((2, 3), F(11))], [3, 4], [None], [F])
			t2 = Table([((0, 0), F(12)), ((0, 1), F(13)), ((0, 2), F(14)), ((0, 3), F(15)), ((1, 0), F(16)), ((1, 1), F(17)), ((1, 2), F(18)), ((1, 3), F(19)), ((2, 0), F(20)), ((2, 1), F(21)), ((2, 2), F(22)), ((2, 3), F(23))], [3, 4], [None], [F])
			
			assert t1[0, 1] == F(1)
			assert t2[2, 2] == F(22)
			
			tn = Table([((0, 0), t1), ((0, 1), t2), ((1, 0), t2), ((1, 1), t2)], [2, 2], [(3, 4), None], [dict, F])
			
			assert tn[0, 0][1, 2] == F(6)
			
			ta = Table([((0, 0), v1), ((0, 1), v1), ((1, 0), v1), ((1, 1), v2)], [2, 2], [4, None], [Vector, F], Array=Array)
			print(v1, v2)
			print(ta[0, 0])
			print(ta[0, 1])
			print(ta[1, 0])
			print(ta[1, 1])
			assert ta[1, 1] == v2
			
			def random_stream(length, size, Array, Field, randbelow):
				for n in range(length):
					yield Vector.random(size, Array, Field, randbelow)
			
			a = Automaton.random_linear_linear(4, 4, 8, Table, Array, Vector, LinearCircuit, Linear, F, randrange)
			with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_linear_linear_{F.__name__}.png')):
				print()
				s = a.init_state[:]
				print(s)
				for n, x in enumerate(a(random_stream(10, 4, Array, F, randrange), s)):
					print(n, x)
				print(s)
			
			b = Automaton.random_linear_quadratic(4, 4, 8, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
			with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_linear_quadratic_{F.__name__}.png')):
				print()
				s = b.init_state[:]
				print(s)
				for n, x in enumerate(b(random_stream(10, 4, Array, F, randrange), s)):
					print(n, x)
				print(s)
			
			c = Automaton.random_quadratic_linear(4, 4, 8, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
			with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_quadratic_linear_{F.__name__}.png')):
				print()
				s = c.init_state[:]
				print(s)
				for n, x in enumerate(c(random_stream(10, 4, Array, F, randrange), s)):
					print(n, x)
				print(s)
			
			d = Automaton.random_quadratic_quadratic(4, 4, 8, Table, Array, Vector, QuadraticCircuit, Quadratic, Linear, F, randrange)
			with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_quadratic_quadratic_{F.__name__}.png')):
				print()
				s = d.init_state[:]
				print(s)
				for n, x in enumerate(d(random_stream(10, 4, Array, F, randrange), s)):
					print(n, x)
				print(s)



