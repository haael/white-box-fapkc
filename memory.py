#!/usr/bin/python3

__all__ = 'Array', 'Table'


from itertools import chain, product


class Array:
	"One-dimensional array of elements that fit in 1 byte. Supports non-scalar subelements of uniform size, as long as they accept Array in the constructor."
	
	Storage = bytes
	
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
		
		except AttributeError:
			if sizes is not None:
				self.__sizes = sizes
			else:
				raise TypeError("`sizes` argument required.")
			
			if types is not None:
				self.__types = types
			else:
				raise TypeError("`types` argument required.")
			
			if isinstance(values, self.Storage):
				self.__storage = values
			elif self.__sizes[0] is None:
				self.__storage = self.Storage(int(_value) for _value in values)
			else:
				self.__storage = self.Storage(chain.from_iterable(_value.serialize() for _value in values))	
			
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
			print(self.__step)
			raise NotImplementedError
		
		size = 1
		for s in self.__sizes:
			if s is not None:
				size *= s
		assert (self.__stop - self.__start) % size == 0, f"{self.__stop} - {self.__start} = {self.__stop - self.__start}; size = {size}"
	
	def __eq__(self, other):
		try:
			return self.__storage == other.__storage
		except AttributeError:
			return NotImplemented
	
	def __len__(self):
		if self.__step != 1:
			raise NotImplementedError
		size = 1
		for s in self.__sizes:
			if s is not None:
				size *= s
		return (self.__stop - self.__start) // size
	
	def serialize(self):
		return self.__storage
	
	def __getitem__(self, index):		
		if hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step'):
			start = index.start
			if start is None:
				start = 0
			
			stop = index.stop
			if stop is None:
				stop = len(self)
			
			step = index.step
			if step is None:
				step = 1
			
			if self.__sizes[0] is None:
				return self.__class__(self, start=self.__start + start, stop=self.__start + stop, step=step)
			else:
				return self.__class__(self, start=self.__start + self.__sizes[0] * start, stop=self.__start + self.__sizes[0] * stop, step=step)
		
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
				return self.__types[0](self.__storage[self.__start + index * self.__step])
			else:
				size = 1
				for s in self.__sizes:
					if s is not None:
						size *= s
				return self.__types[0](self.__class__(self, sizes=self.__sizes[1:], types=self.__types[1:], start=self.__start + size * index * self.__step, stop=self.__start + size * (index * self.__step + 1)))


class Table:
	"Multi-dimensional table of elements that fit in 1 byte. Supports non-scalar subelements of uniform size, as long as they accept Table in the constructor."
	
	Storage = bytes
	
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
			
			if isinstance(items, self.Storage):
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
							yield int(items[index])
				
				self.__storage = self.Storage(values())
			
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
		return self.__storage
	
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
			return self.__types[0](self.Array(self.__storage, sizes=self.__sizes[1:], types=self.__types[1:], start=offset * size, stop=(offset + 1) * size))
		else:
			return self.__types[0](self.__class__(self, ksize=self.__sizes[0], sizes=self.__sizes[1:], types=self.__types[1:], start=offset * size, stop=(offset + 1) * size, Array=self.Array))


if __debug__ and __name__ == '__main__':
	from random import randrange
	from fields import Galois
	from linear import *
	from machines import *
	
	#F = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	F = Galois('F', 3, [1, 0, 2, 1])
	
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
	
	ans = an[1:3]
	print(ans[0])
	assert ans[0] == an[1]
	assert ans[1] == an[2]
	assert ans[2] == an[3]
	
	an1 = Array([a1, a2, a3], [4, None], [Array, F])
	an2 = Array([a3, a1, a2], [4, None], [Array, F])
	
	ann = Array([an1, an2], [3, 4, None], [Array, Array, F])
	
	assert ann[1][0][2] == F(10)
	
	l1 = Linear(Array([F(1), F(2), F(3)], [None], [F]))
	l2 = Linear.random(Array, F, randrange)
	print(l1, l2, l1 + l2)
	
	q1 = Quadratic(Array([Linear(Array([F(1), F(2), F(3)], [None], [F])), Linear(Array([F(4), F(5), F(6)], [None], [F])), Linear(Array([F(7), F(8), F(0)], [None], [F]))], [3, None], [Linear, F]))
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
	
	print()
	a = Automaton.random_linear_linear(4, 3, 4, Table, Array, Vector, LinearCircuit, Linear, F, randrange)
	for n, x in enumerate(a(random_stream(32, 3, Array, F, randrange))):
		print(n, x)
	
	print()
	b = Automaton.random_linear_quadratic(4, 3, 4, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
	for n, x in enumerate(b(random_stream(32, 3, Array, F, randrange))):
		print(n, x)
	
	print()
	c = Automaton.random_quadratic_linear(4, 3, 4, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, F, randrange)
	for n, x in enumerate(c(random_stream(32, 3, Array, F, randrange))):
		print(n, x)
	
	print()
	d = Automaton.random_quadratic_quadratic(4, 3, 4, Table, Array, Vector, QuadraticCircuit, Quadratic, Linear, F, randrange)
	for n, x in enumerate(d(random_stream(32, 3, Array, F, randrange))):
		print(n, x)



