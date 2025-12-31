#!/usr/bin/python3


"This module provides classes `Array` (list-like) and `Table` (dict-like) that can be used to implement different memory layout for circuits and finite automata."


__all__ = 'Backing', 'Array', 'Table'


from itertools import chain, product
from utils import cached, classproperty
from functools import reduce, cmp_to_key
from operator import __mul__
from copy import deepcopy


def mul(factors):
	return reduce(__mul__, factors, 1)


class Backing:
	StorageType = bytearray # type of storage buffer
	Storage = bytearray # function to create storage buffer
	cast = int # function to pass each storage element through
	result = memoryview # slice-supporting function to obtain result from storage
	
	def __init__(self, storage, sizes, types, offset, slice_):
		self.sizes = sizes
		self.types = types
		self.offset = offset
		self.storage = storage
		self.slice_ = slice_
		
		if self.slice_ is Ellipsis:
			self.slice_ = slice(0, self.sizes[0], 1) if not isinstance(self.sizes[0], tuple) else tuple(slice(0, _s, 1) for _s in self.sizes[0])
		
		if isinstance(self.slice_, tuple) and isinstance(self.sizes[0], tuple):
			if len(self.slice_) != len(self.sizes[0]):
				raise ValueError
		elif isinstance(self.slice_, slice) and isinstance(self.sizes[0], int):
			pass
		else:
			raise ValueError(f"Either both `slice_` and `sizes` must be a tuple of equal length or both must be integer. slice_:{type(slice_).__name__}; sizes:{type(sizes).__name__}")
		
		for ssize in self.sizes:
			if isinstance(ssize, tuple):
				for zsize in ssize:
					if not zsize.is_integer():
						raise ValueError("All `sizes` must be integer or tuple of integers.")
					if not 0 <= zsize:
						raise ValueError("All `sizes` must be nonnegative.")
			else:
				if not ssize.is_integer():
					raise ValueError("All `sizes` must be integer or tuple of integers.")
				if not 0 <= ssize:
					raise ValueError(f"All `sizes` must be nonnegative (got {ssize}).")
		
		if len(self.sizes) != len(self.types) + 1:
			raise ValueError("`sizes` must be 1 element more than `types`.")
		
		if not 0 <= self.offset:
			raise ValueError("`offset` must be nonnegative")
		if not self.offset.is_integer():
			raise ValueError("`offset` must be integer")
	
	@classmethod
	def deserialize(cls, data, sizes, types, Array, Table):
		if isinstance(sizes[0], int):
			if len(types) == 1:
				return Array((types[0].deserialize(data) for _n in range(sizes[0])), sizes, types)
			else:
				return Array((cls.deserialize(data, sizes[1:], types[1:], Array, Table) for _n in range(sizes[0])), sizes, types)
		elif isinstance(sizes[0], tuple):
			if len(types) == 1:
				return Table(((_key, types[0].deserialize(data)) for _key in product(*[range(_s) for _s in sizes[0]])), sizes, types, Array=Array)
			else:
				return Table(((_key, cls.deserialize(data, sizes[1:], types[1:], Array, Table)) for _key in range(*[range(_s) for _s in sizes[0]])), sizes, types, Array=Array)
		else:
			raise ValueError


class Array(Backing):
	"One-dimensional array of elements. Supports non-scalar subelements of uniform size, as long as they accept Array in the constructor."
	
	@classproperty
	def Array(cls):
		return cls
	
	def __init__(self, storage, sizes=None, types=None, offset=None, slice_=None):
		try:
			if sizes is None: sizes = storage.sizes
			if types is None: types = storage.types
			if offset is None: offset = storage.offset
			if slice_ is None: slice_ = storage.slice_
			storage = storage.storage
		except AttributeError:
			if sizes is None: raise ValueError("`sizes` required")
			if types is None: raise ValueError("`types` required")
			if offset is None: offset = 0
			if slice_ is None: slice_ = Ellipsis
		
		if not isinstance(storage, self.StorageType):
			storage = self.__class__.Storage(chain.from_iterable(_value.serialize() for _value in storage))
		
		if not isinstance(sizes[0], int):
			raise ValueError("Array constructor must have integer at first position of `sizes` argument.")
		super().__init__(storage, sizes, types, offset, slice_)
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + ', '.join(repr(_x) for _x in [self.__storage, self.__sizes, [_type.__name__ for _type in self.__types], self.__offset, self.__start, self.__stop, self.__step])  + ')'
	
	def __eq__(self, other):
		try:
			if len(self) != len(other):
				return False
			
			for n in range(len(self)):
				if self[n] != other[n]:
					return False
			
			return True
		
		except (AttributeError, TypeError):
			return NotImplemented
	
	def __len__(self):
		if len(self.sizes) == 1:
			raise ValueError
		else:
			if self.slice_.step != 1:
				raise NotImplementedError
			return self.slice_.stop - self.slice_.start
	
	def __getitem__(self, index):
		size, *sizes = self.sizes
		assert isinstance(size, int)
		element_size = mul(_s if isinstance(_s, int) else mul(_s) for _s in sizes)
		
		type_, *types = self.types
		
		start = self.slice_.start
		stop = self.slice_.stop
		step = self.slice_.step
		if not step == 1:
			raise NotImplementedError
		
		if isinstance(index, int): # numeric index
			if not 0 <= index < (stop - start):
				raise IndexError
			
			offset = self.offset + (start + index) * element_size
			
			if not types:
				return type_.deserialize(iter(self.__class__.result(self.storage)[offset : offset + element_size]))
			else:
				if isinstance(sizes[0], int):
					cls = Array
				elif isinstance(sizes[0], tuple):
					cls = Table
				else:
					raise ValueError
				
				return type_(cls(self, sizes=sizes, types=types, offset=offset, slice_=...))
		
		elif index is Ellipsis or (hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step')): # slice or ellipsis
			if index is Ellipsis:
				index = slice(0, size, 1)
			
			istart = index.start if index.start is not None else 0
			istop = index.stop if index.stop is not None else size
			istep = index.step if index.step is not None else 1
			
			if istep != 1:
				raise NotImplementedError
			if not istart <= istop:
				raise NotImplementedError
			
			if not 0 <= istart < (stop - start):
				raise IndexError
			if not 0 <= istop <= (stop - start):
				raise IndexError
			
			new_slice = slice(start + istart, start + istop, 1)
			return self.__class__(self, slice_=new_slice)
		
		else:
			raise ValueError
		
	def __setitem__(self, index, value):
		size, *sizes = self.sizes
		assert isinstance(size, int)
		element_size = mul(_s if isinstance(_s, int) else mul(_s) for _s in sizes)
		
		type_, *types = self.types
		
		start = self.slice_.start
		stop = self.slice_.stop
		step = self.slice_.step
		if not step == 1:
			raise NotImplementedError
		
		if isinstance(index, int): # numeric index
			if not 0 <= index < (stop - start):
				raise IndexError
			
			offset = self.offset + (start + index) * element_size
			
			if not types:
				self.storage[offset : offset + element_size] = self.__class__.Storage(value.serialize() if hasattr(value, 'serialize') else [self.__class__.cast(_element) for _element in value])
			else:
				if isinstance(sizes[0], int):
					cls = Array
				elif isinstance(sizes[0], tuple):
					cls = Table
				else:
					raise ValueError
				
				cls(self, sizes=sizes, types=types, offset=offset, slice_=...)[...] = value
		
		elif index is Ellipsis or (hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step')): # slice or ellipsis
			if index is Ellipsis:
				index = slice(0, size, 1)
			
			istart = index.start if index.start is not None else 0
			istop = index.stop if index.stop is not None else size
			istep = index.step if index.step is not None else 1
			
			if istep != 1:
				raise NotImplementedError
			if not istart <= istop:
				raise NotImplementedError
			
			if not 0 <= istart < (stop - start):
				raise IndexError
			if not 0 <= istop <= (stop - start):
				raise IndexError
			
			new_slice = slice(start + istart, start + istop, 1)
			helper = self.__class__(self, slice_=new_slice)
			for n, item in enumerate(value):
				helper[n] = item
		
		else:
			raise ValueError
	
	def serialize(self):
		element_size = mul(_s if isinstance(_s, int) else mul(_s) for _s in self.sizes[1:])
		
		start = self.slice_.start
		stop = self.slice_.stop
		step = self.slice_.step
		
		assert start is not None
		assert stop is not None
		assert step is not None
		
		if step != 1:
			raise NotImplementedError
		
		yield from iter(self.__class__.result(self.storage)[self.offset + start * element_size : self.offset + stop * element_size])


class Table(Backing):
	"Multi-dimensional table of elements. Supports non-scalar subelements of uniform size, as long as they accept Table in the constructor."
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + ', '.join(repr(_x) for _x in [self.storage, self.sizes, [_type.__name__ for _type in self.types], self.offset, self.slice_])  + ', Array=' +  self.Array.__name__ + ')'
	
	@classproperty
	def Table(cls):
		return cls
	
	@staticmethod
	def __keyorder(t1, t2):
		if len(t1) != len(t2):
			raise ValueError
		
		for a, b in zip(t1, t2):
			if a < b:
				return True
			elif a > b:
				return False
		
		return False
	
	def __init__(self, storage, sizes=None, types=None, offset=None, slice_=None, Array=None):
		try:
			if sizes is None: sizes = storage.sizes
			if types is None: types = storage.types
			if offset is None: offset = storage.offset
			if slice_ is None: slice_ = storage.slice_
			if Array is None: Array = storage.Array
			storage = storage.storage
		except AttributeError:
			if sizes is None: raise ValueError("`sizes` required")
			if types is None: raise ValueError("`types` required")
			if offset is None: offset = 0
			if slice_ is None: slice_ = Ellipsis	
			if Array is None: raise ValueError("`Array` argument required")
		
		if not isinstance(storage, self.StorageType):
			storage_dict = dict(storage.items() if hasattr(storage, 'items') else storage)
			all_keys = frozenset(product(*[range(_s) for _s in sizes[0]]))
			if all_keys != frozenset(storage_dict.keys()):
				raise ValueError(f"Keys mismatch: {list(all_keys)} != {list(storage_dict.keys())}")
			storage = self.__class__.Storage(chain.from_iterable(_value.serialize() for (_key, _value) in sorted(list(storage_dict.items()), key=cmp_to_key(self.__keyorder))))
		
		if not isinstance(sizes[0], tuple):
			raise ValueError("Table constructor must have tuple of integers at first position of `sizes` argument.")
		
		super().__init__(storage, sizes, types, offset, slice_)
		self.Array = Array
	
	def __eq__(self, other):
		size = self.sizes[0]
		assert isinstance(size, tuple)
		
		try:
			if frozenset(self.keys()) != frozenset(other.keys()):
				return False
			
			for ns in product(*[range(_l.stop - _l.start) for _l in self.slice_]):
				if self[ns] != other[ns]:
					return False
			
			return True
		
		except (AttributeError, TypeError):
			return NotImplemented
	
	def keys(self):
		size = self.sizes[0]
		assert isinstance(size, tuple)
		assert isinstance(self.slice_, tuple)
		assert len(size) == len(self.slice_)
		yield from product(*[range(_l.stop - _l.start) for _l in self.slice_])
	
	def values(self):
		for index in self.keys():
			yield self[index]
	
	def items(self):
		for index in self.keys():
			yield index, self[index]
	
	def __getitem__(self, index):
		size, *sizes = self.sizes
		assert isinstance(size, tuple)
		element_size = mul(_s if isinstance(_s, int) else mul(_s) for _s in sizes)
		
		type_, *types = self.types
		
		if index is Ellipsis:
			index = []
			for s in size:
				index.append(slice(0, s, 1))
			index = tuple(index)
		
		if not isinstance(index, tuple):
			raise KeyError(f"Index must be a {len(size)}-tuple. (Got {type(index).__name__}.)")
		if len(index) != len(size):
			raise KeyError(f"Index must be a {len(size)}-tuple. (Got {len(index)}-tuple.)")
		
		if all(isinstance(_element, int) for _element in index): # fully numeric index
			position = 0
			for n, (eindex, eslice) in enumerate(zip(index, self.slice_)):
				estart = eslice.start
				estop = eslice.stop
				estep = eslice.step
				if not estep == 1:
					raise NotImplementedError
				
				if not 0 <= eindex < (estop - estart):
					raise KeyError
				
				position += (estart + eindex) * mul(_rslice.stop - _rslice.start for _rslice in self.slice_[n+1:])
			
			offset = self.offset + position * element_size
			
			if not types:
				return type_.deserialize(iter(self.__class__.result(self.storage)[offset : offset + element_size]))
			else:
				if isinstance(sizes[0], int):
					cls = Array
				elif isinstance(sizes[0], tuple):
					cls = Table
				else:
					raise ValueError
				
				return type_(cls(self, sizes=sizes, types=types, offset=offset, slice_=...))
		
		else:
			new_slice = []
			for n, (eindex, eslice) in enumerate(zip(index, self.slice_)):
				estart = eslice.start
				estop = eslice.stop
				estep = eslice.step
				if not estep == 1:
					raise NotImplementedError
				
				if isinstance(eindex, int):
					if not 0 <= eindex < (estop - estart):
						raise KeyError
					new_slice.append(slice(estart + eindex, estart + eindex + 1, 1))
				else:
					istart = eindex.start if eindex.start is not None else 0
					istop = eindex.stop if eindex.stop is not None else estop - estart
					istep = eindex.step if eindex.step is not None else 1
					if not istep == 1:
						raise NotImplementedError(f"Slice steps other than 1 are not implemented (got {istep}).")
					if not 0 <= istart < (estop - estart):
						raise KeyError
					if not 0 <= istop <= (estop - estart):
						raise KeyError
					if not istart <= istop:
						raise ValueError
					new_slice.append(slice(estart + istart, estart + istop, 1))
			
			return self.__class__(self, slice_=tuple(new_slice))
	
	def __setitem__(self, index, value):
		size, *sizes = self.sizes
		assert isinstance(size, tuple)
		element_size = mul(_s if isinstance(_s, int) else mul(_s) for _s in sizes)
		
		type_, *types = self.types
		
		if index is Ellipsis:
			index = []
			for s in size:
				index.append(slice(0, s, 1))
			index = tuple(index)
		
		if not isinstance(index, tuple):
			raise KeyError(f"Index must be a {len(size)}-tuple. (Got {type(index).__name__}.)")
		if len(index) != len(size):
			raise KeyError(f"Index must be a {len(size)}-tuple. (Got {len(index)}-tuple.)")
		
		if all(isinstance(_element, int) for _element in index): # fully numeric index
			position = 0
			for n, (eindex, eslice) in enumerate(zip(index, self.slice_)):
				estart = eslice.start
				estop = eslice.stop
				estep = eslice.step
				if not estep == 1:
					raise NotImplementedError
				
				if not 0 <= eindex < (estop - estart):
					raise KeyError
				
				position += (estart + eindex) * mul(_rslice.stop - _rslice.start for _rslice in self.slice_[n+1:])
			
			offset = self.offset + position * element_size
			
			if not types:
				self.storage[offset : offset + element_size] = self.__class__.Storage(value.serialize())
			else:
				if isinstance(sizes[0], int):
					cls = Array
				elif isinstance(sizes[0], tuple):
					cls = Table
				else:
					raise ValueError
				
				cls(self, sizes=sizes, types=types, offset=offset, slice_=...)[...] = value
		
		else:
			new_slice = []
			for n, (eindex, eslice) in enumerate(zip(index, self.slice_)):
				estart = eslice.start
				estop = eslice.stop
				estep = eslice.step
				if not estep == 1:
					raise NotImplementedError
				
				if isinstance(eindex, int):
					if not 0 <= eindex < (estop - estart):
						raise KeyError
					new_slice.append(slice(estart + eindex, estart + eindex + 1, 1))
				else:
					istart = eindex.start if eindex.start is not None else 0
					istop = eindex.stop if eindex.stop is not None else estop - estart
					istep = eindex.step if eindex.step is not None else 1
					if not istep == 1:
						raise NotImplementedError(f"Slice steps other than 1 are not implemented (got {istep}).")
					if not 0 <= istart < (estop - estart):
						raise KeyError
					if not 0 <= istop <= (estop - estart):
						raise KeyError
					if not istart <= istop:
						raise ValueError
					new_slice.append(slice(estart + istart, estart + istop, 1))
			
			helper = self.__class__(self, slice_=tuple(new_slice))
			for key, evalue in value.items():
				helper[key] = evalue
	
	def serialize(self):
		element_size = mul(_s if isinstance(_s, int) else mul(_s) for _s in self.sizes[1:])

		start = self.slice_[0].start
		stop = self.slice_[0].stop
		step = self.slice_[0].step
		if not step == 1:
			raise NotImplementedError
		
		for key in sorted(self.keys(), key=cmp_to_key(self.__keyorder)):
			position = 0
			for n, (eindex, eslice) in enumerate(zip(key, self.slice_)):
				estart = eslice.start
				estop = eslice.stop
				estep = eslice.step
				if not estep == 1:
					raise NotImplementedError
				
				if not 0 <= eindex < (estop - estart):
					raise KeyError
				
				position += (estart + eindex) * mul(self.sizes[0][n+1:])
			
			offset = self.offset + position * element_size
			yield from iter(self.__class__.result(self.storage)[offset : offset + element_size])


if __debug__:
	def array_test_smoke(Array, F):
		"Smoke test of Array implementation."
		
		print(" Array smoke test.")
		
		a0 = Array([F(0 % F.field_size), F(1 % F.field_size), F(2 % F.field_size), F(3 % F.field_size)], [4, F.field_bytesize], [F])
		
		assert len(a0) == 4
		assert isinstance(a0[0], F)
		assert a0[0] == F(0 % F.field_size)
		assert a0[1] == F(1 % F.field_size)
		assert a0[2] == F(2 % F.field_size)
		assert a0[3] == F(3 % F.field_size)
		
		a1 = Array([F(4 % F.field_size), F(5 % F.field_size), F(6 % F.field_size), F(7 % F.field_size)], [4, F.field_bytesize], [F])
		a2 = Array([F(8 % F.field_size), F(9 % F.field_size), F(10 % F.field_size), F(11 % F.field_size)], [4, F.field_bytesize], [F])
		
		an = Array([a0, a1, a2], [3, 4, F.field_bytesize], [Array, F])
		assert an.sizes == [3, 4, F.field_bytesize]
		assert an[0] == a0
		assert an[1] == a1
		assert an[2] == a2
		
		assert an[0][0] == F(0 % F.field_size)
		assert an[0][1] == F(1 % F.field_size)
		assert an[1][0] == F(4 % F.field_size)
		assert an[2][3] == F(11 % F.field_size)
		assert isinstance(a2[0], F)
		
		ans = an[1:3]
		assert ans[0] == an[1]
		assert ans[1] == an[2]
		
		ans = an[...]
		assert ans[0] == an[0]
		assert ans[1] == an[1]
		assert ans[2] == an[2]
		
		an1 = Array([a0, a1, a2], [3, 4, F.field_bytesize], [Array, F])
		an2 = Array([a1, a2, a0], [3, 4, F.field_bytesize], [Array, F])
		
		ann = deepcopy(Array([an1, an2], [2, 3, 4, F.field_bytesize], [Array, Array, F]))
		
		assert ann[1][0][2] == F(6 % F.field_size)
		
		ann[1][0][2] = F(11 % F.field_size)
		assert ann[1][0][2] == F(11 % F.field_size)
		
		ann[1][1] = [F(1 % F.field_size), F(2 % F.field_size), F(3 % F.field_size), F(4 % F.field_size)]
		assert ann[1][1][2] == F(3 % F.field_size)
		
		ann[1][1][:] = [F(5 % F.field_size), F(6 % F.field_size), F(7 % F.field_size), F(8 % F.field_size)]
		assert ann[1][1][2] == F(7 % F.field_size)
		
		ann[1][1][...] = [F(9 % F.field_size), F(10 % F.field_size), F(11 % F.field_size), F(12 % F.field_size)]
		assert ann[1][1][2] == F(11 % F.field_size)
		
		ann[...] = [[[F((m * n + k) % F.field_size) for n in range(4)] for m in range(3)] for k in range(2)]
		assert ann[0][2][3] == F(6 % F.field_size)
		assert ann[0][1][2] == F(2 % F.field_size)
		assert ann[1][2][3] == F(7 % F.field_size)
		assert ann[1][1][2] == F(3 % F.field_size)
	
	def table_test_smoke(Table, Array, F):
		"Smoke test of Table implementation."
		
		print(" Table smoke test.")
		
		t00 = Table({(0, 0): F(0 % F.field_size), (0, 1): F(1 % F.field_size), (0, 2): F(2 % F.field_size), (1, 0): F(3 % F.field_size), (1, 1): F(4 % F.field_size), (1, 2): F(5 % F.field_size),}, [(2, 3), F.field_bytesize], [F], Array=Array)
		
		assert frozenset(t00.keys()) == frozenset(product(range(2), range(3)))
		assert t00[0, 1] == F(1 % F.field_size)
		assert frozenset(t00.values()) == frozenset(F(_n % F.field_size) for _n in range(6))
		for key, value in t00.items():
			assert t00[key] == value
		
		t01 = Table({(0, 0): F(10 % F.field_size), (0, 1): F(11 % F.field_size), (0, 2): F(12 % F.field_size), (1, 0): F(13 % F.field_size), (1, 1): F(14 % F.field_size), (1, 2): F(15 % F.field_size),}, [(2, 3), F.field_bytesize], [F], Array=Array)
		t10 = Table({(0, 0): F(20 % F.field_size), (0, 1): F(21 % F.field_size), (0, 2): F(22 % F.field_size), (1, 0): F(23 % F.field_size), (1, 1): F(24 % F.field_size), (1, 2): F(25 % F.field_size),}, [(2, 3), F.field_bytesize], [F], Array=Array)
		t11 = Table({(0, 0): F(30 % F.field_size), (0, 1): F(31 % F.field_size), (0, 2): F(32 % F.field_size), (1, 0): F(33 % F.field_size), (1, 1): F(34 % F.field_size), (1, 2): F(35 % F.field_size),}, [(2, 3), F.field_bytesize], [F], Array=Array)
		
		for key, value in t01.items():
			assert t01[key] == value
		for key, value in t10.items():
			assert t10[key] == value
		for key, value in t11.items():
			assert t11[key] == value
		
		tss = Table({(0, 0): t00, (0, 1): t01, (1, 0): t10, (1, 1): t11}, [(2, 2), (2, 3), F.field_bytesize], [Table, F], Array=Array)
		
		assert tss[0, 0] == t00
		assert tss[0, 1] == t01
		assert tss[1, 0] == t10
		assert tss[1, 1] == t11
		
		assert t00[0, 0] == tss[0, 0][0, 0]
		assert t00[0, 2] == tss[0, 0][0, 2]
		assert t10[1, 2] == tss[1, 0][1, 2]
		
		assert list(tss.serialize()) == list(chain(t00.serialize(), t01.serialize(), t10.serialize(), t11.serialize()))
		assert list(tss[1:, :1].serialize()) == list(t10.serialize())
		
		tzz = deepcopy(tss)
		assert list(tss.serialize()) == list(tss[...].serialize()) == list(tss[:, :].serialize()) == list(tzz.serialize())
		
		for m, n, o, p in product(range(2), range(2), range(2), range(3)):
			tzz[m, n][o, p] += F(1)
		
		for m, n, o, p in product(range(2), range(2), range(2), range(3)):
			assert tzz[m, n][o, p] == tss[m, n][o, p] + F(1)
	
	def array_test_serialization(Array, Field, randbelow):
		"Test Array serialize/deserialize protocol."
		
		print(" Array serialization test.")
		for n in range(1, 200):
			for m in range(10):
				a = Array((Field.random(randbelow) for _k in range(n)), [n, Field.field_bytesize], [Field])
				assert len(a) == n
				#print("instance", type(next(a.serialize())), a.cast)
				assert isinstance(next(a.serialize()), a.cast)
				data = a.serialize()
				b = Array.deserialize(data, [n, Field.field_bytesize], [Field], Array, None)
				assert len(b) == n
				assert a == b
	
	def table_test_serialization(Table, Array, Field, randbelow):
		"Test Array serialize/deserialize protocol."
		
		print(" Table serialization test.")
		for m, n in product(range(1, 10), range(1, 20)):
			for k in range(10):
				a = Table(((_key, Field.random(randbelow)) for _key in product(range(m), range(n))), [(m, n), Field.field_bytesize], [Field], Array=Array)
				assert a.sizes[0] == (m, n)
				#print("instance", type(next(a.serialize())), a.cast)
				assert isinstance(next(a.serialize()), a.cast)
				data = a.serialize()
				b = Table.deserialize(data, [(m, n), Field.field_bytesize], [Field], Array, Table)
				assert b.sizes[0] == (m, n)
				assert a == b
	
	def array_test_vector(Vector, Array, Field, randbelow):
		"Test Array through Vector operations."
		
		print(" Array/Vector test.")
		for n in range(1, 50):
			for m in range(10):
				a = Vector(Array((Field.random(randbelow) for _k in range(n)), [n, Field.field_bytesize], [Field]))
				b = Vector(Array((Field.random(randbelow) for _k in range(n)), [n, Field.field_bytesize], [Field]))
				
				c = a + b
				assert len(c) == len(b) == len(a)
				for x, y, z in zip(a, b, c):
					assert x + y == z
				
				c = a - b
				assert len(c) == len(b) == len(a)
				for x, y, z in zip(a, b, c):
					assert x - y == z
				
				c = a * b
				assert len(c) == len(b) == len(a)
				for x, y, z in zip(a, b, c):
					assert x * y == z
				
				c = -a
				assert len(c) == len(a)
				for x, z in zip(a, c):
					assert -x == z
				
				c = a @ b
				assert isinstance(c, Field)
				z = Field.zero()
				for x, y in zip(a, b):
					z += x * y
				assert c == z
	
	def table_test_matrix(Matrix, Vector, Table, Array, Field, randbelow):
		"Test Table through Matrix operations."
		
		print(" Table/Matrix test.")
		for m, n in product(range(1, 10), range(1, 20)):
			for o in range(5):
				a = Matrix(Table((((_k, _l), Field.random(randbelow)) for (_k, _l) in product(range(m), range(n))), [(m, n), Field.field_bytesize], [Field], Array=Array))
				b = Matrix(Table((((_k, _l), Field.random(randbelow)) for (_k, _l) in product(range(m), range(n))), [(m, n), Field.field_bytesize], [Field], Array=Array))
				
				c = a + b
				assert c.matrix_width == a.matrix_width == b.matrix_width and c.matrix_height == a.matrix_height == b.matrix_height
				for x, y, z in zip(a.values(), b.values(), c.values()):
					assert x + y == z
				
				c = a - b
				assert c.matrix_width == a.matrix_width == b.matrix_width and c.matrix_height == a.matrix_height == b.matrix_height
				for x, y, z in zip(a.values(), b.values(), c.values()):
					assert x - y == z
				
				f = Field.random(randbelow)
				c = a * f
				assert c.matrix_width == a.matrix_width and c.matrix_height == a.matrix_height
				for x, z in zip(a.values(), c.values()):
					assert x * f == z
				
				c = -a
				assert c.matrix_width == a.matrix_width and c.matrix_height == a.matrix_height
				for x, z in zip(a.values(), c.values()):
					assert -x == z
				
				if a.matrix_height == b.matrix_width:
					c = a @ b
					assert c.matrix_width == a.matrix_width and c.matrix_height == b.matrix_height
					for i, j in product(range(c.matrix_height), range(c.matrix_width)):
						z = Field.zero()
						for k in range(a.matrix_height):
							z += a[i, k] * b[k, j]
						assert c[i, j] == z


if __debug__ and __name__ == '__main__':
	profile = False
	if profile:
		from pycallgraph2 import PyCallGraph
		from pycallgraph2.output.graphviz import GraphvizOutput
	
	from random import randrange
	from fields import Galois, Field
	from vectors import *
	
	from numpy import array, uint8, fromiter, bitwise_xor
		
	class Modulo7919(Field):
		modulus = 7919
	
	assert Modulo7919.field_bytesize == 2
	
	PyArray = Array
	PyTable = Table
	
	class NpArray(PyArray):
		StorageType = type(array([0], dtype=uint8))
		Storage = lambda x: fromiter(x, dtype=uint8)
		result = lambda x: x
		cast = uint8
	
	class NpTable(PyTable):
		StorageType = type(array([0], dtype=uint8))
		Storage = lambda x: fromiter(x, dtype=uint8)
		result = lambda x: x
		cast = uint8
	
	for m_impl in ('py', 'np', 'np+'):
		if m_impl == 'py':
			print()
			print("Testing implementation: plain Python")
		elif m_impl == 'np':
			print()
			print("Testing implementation: numpy with Python summation")
		elif m_impl == 'np+':
			print()
			print("Testing implementation: numpy with native summation")
		
		if m_impl == 'py':
			Array = PyArray
			Table = PyTable
		elif m_impl in ('np', 'np+'):
			Array = NpArray
			Table = NpTable
		
		for F in Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1]), Galois('F3', 3, [1, 0, 2, 1]), Galois('Binary', 2, [1, 1]), Modulo7919:
			if m_impl == 'np+' and F.__name__ == 'Rijndael':
				class F(F):
					@classmethod
					def sum(cls, values):
						return cls(bitwise_xor.reduce(array(fromiter(values, dtype=uint8), dtype=uint8)))
					
					def serialize(self):
						try:
							yield from self._BinaryGalois__value.tobytes()
						except AttributeError:
							yield from super().serialize()
				
				F.__name__ = 'Rijndael'
			
			print("storage:", type(Array([F.zero()], [1, F.field_bytesize], [F]).storage).__name__, "field:", F.__name__)
			
			array_test_smoke(Array, F)
			array_test_serialization(Array, F, randrange)
			array_test_vector(Vector, Array, F, randrange)
			
			table_test_smoke(Table, Array, F)
			table_test_serialization(Table, Array, F, randrange)
			table_test_matrix(Matrix, Vector, Table, Array, F, randrange)


