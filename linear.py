#!/usr/bin/python3
#-*- coding:utf8 -*-

"Implementation of linear algebra: vectors (or modules) over rings (or fields) and matrices."

from enum import Enum
from collections import Counter
from itertools import chain, product
import operator

from utils import randbelow, random_permutation, random_sample, parallel_map, parallel_starmap, canonical, optimized, evaluate, substitute
from algebra import AlgebraicStructure
from rings import BooleanRing


__all__ = 'Vector', 'Matrix'


class Vector(AlgebraicStructure):
	"Vectors over fields or modules over rings or their polynomials. Mutable, but dimension is always constant."
	
	algebra_kwparams_names = ('base_ring',)
	default_ring = BooleanRing.get_algebra()
	
	def __init__(self, init, dimension=None, base_ring=None):
		"""
		If `dimension` is specified, create a vector of that size. `base_ring`
		must also be specified and `init` should be an int whose bits are decoded
		to elements of Galois field.
		If `dimension` is not specified, `init` should be a collection with
		length and the vector is initialized with it. If `base_ring` is specified,
		the elements of `init` will be checked if they are from the right field.
		"""
		
		try:
			if base_ring.algebra_name == 'Polynomial':
				size = base_ring.base_ring.size
			else:
				size = base_ring.size
			self.value = list(base_ring((init // size**_n) % size) for _n in range(dimension))
		except (TypeError, AttributeError):
			if base_ring == None:
				self.value = list(init)
				try:
					base_ring = self.value[0].algebra
				except IndexError:
					raise ValueError("For vectors of 0 dimension `base_ring` is mandatory.")
			else:
				self.value = [base_ring(_i) for _i in init]
		
		assert len(self) == dimension if (dimension != None) else True
		assert all(self[_key] == _value for (_key, _value) in zip(self.keys(), self.values()))		
		if not all((_value.algebra == base_ring or (base_ring.algebra_name == 'Polynomial' and _value.algebra == base_ring.base_ring)) for _value in self):
			raise ValueError("All components of the vector {} must be from the same ring {}.".format([str(_v) for _v in self], base_ring))
		
		AlgebraicStructure.__init__(self, base_ring=base_ring)
	
	@classmethod
	def zero(cls, dimension, base_ring=default_ring):
		"Return zero vector of the specified length, filled with zeroes from the specified ring."
		return cls((base_ring.zero() for _i in range(dimension)), base_ring=base_ring)
	
	@classmethod
	def base(cls, dimension, index, base_ring=default_ring):
		"Return a vector whose all elements are ring 0, except the one at the position `index` which equals ring 1. `dimension` is the vector length, `base_ring` is the desired ring algebra."
		return cls(((base_ring.one() if (_i == index) else base_ring.zero()) for _i in range(dimension)), base_ring=base_ring)
	
	@classmethod
	def random(cls, dimension, variables=None, order=0, base_ring=default_ring):
		"Return random vector of the specified length. If `variables` are specified, generates random polynomial vector."
		if variables:
			return cls((base_ring.random(variables=variables, order=order) for _i in range(dimension)), base_ring=base_ring)
		else:
			return cls((base_ring.random() for _i in range(dimension)), base_ring=base_ring)
	
	@classmethod
	def random_nonzero(cls, dimension, base_ring=default_ring): # FIXME: at least one component should be nonzero
		"Return random vector of the specified length. If `variables` are specified, generates random polynomial vector."
		if variables:
			return cls((base_ring.random_nonzero(variables=variables, order=order) for _i in range(dimension)), base_ring=base_ring)
		else:
			return cls((base_ring.random_nonzero() for _i in range(dimension)), base_ring=base_ring)
	
	@classmethod
	def domain(cls, dimension, base_ring=default_ring):
		"Yield all possible vectors of the specified length, filled with all possible values of the specified ring. The stream has `2**(length * field_size)` elements, so it may take very long to finish."
		if dimension == 0:
			yield cls([], base_ring=base_ring)
		elif dimension < 0:
			raise ValueError("Length of the vector must not be negative.")
		else:
			for vector, component in product(cls.domain(dimension - 1, base_ring=base_ring), base_ring.domain()):
				yield cls(chain([component], vector), base_ring=base_ring)
	
	@property
	def dimension(self):
		"Return dimension of the vector, that means its length."
		return len(self)
	
	__hash__ = None
	
	def __str__(self):
		return "Vector([" + ", ".join([str(_x) for _x in self]) + "])"
	
	def __repr__(self):
		return "Vector([" + ", ".join([repr(_x) for _x in self]) + "])"
	
	def __len__(self):
		return len(self.value)
	
	def __iter__(self):
		yield from self.value
	
	def __getitem__(self, i):
		if i != Ellipsis:
			try:
				if i >= self.dimension or i < -self.dimension:
					raise IndexError("Vector index out of range (index={}; dimension={})".format(i, self.dimension))
				return self.value[i]
			except TypeError:
				if i.start != None and (i.start >= self.dimension or i.start < -self.dimension):
					raise IndexError("Vector slice start out of range (start={}; dimension={})".format(i.start, self.dimension))
				if i.stop != None and (i.stop >= self.dimension or i.stop < -self.dimension):
					raise IndexError("Vector slice stop out of range (stop={}; dimension={})".format(i.stop, self.dimension))
			return self.algebra(self.value[i])
		else:
			return self.algebra(self)
	
	def __setitem__(self, i, value):
		if i == Ellipsis:
			if len(value) != len(self):
				raise ValueError("Assigned sequence must have the same length as the original vector (expected {}, got {}).".format(len(self), len(value)))
			
			i = slice(0, len(self))
			
			if any(_v.algebra != self.algebra.base_ring for _v in value):
				raise ValueError("The assigned sequence must consist of elements of the same field as the original vector (field_size={}).".format(self.field_size))
		else:
			try:
				if i >= self.dimension or i < -self.dimension:
					raise IndexError("Vector index out of range (index={}; dimension={})".format(i, self.dimension))
				if value.algebra != self.algebra.base_ring:
					raise ValueError("The assigned value must be an element of the same field as the original vector (field_size={}).".format(self.field_size))
			except TypeError:
				if i.start >= self.dimension or i.start < -self.dimension:
					raise IndexError("Vector slice start out of range (start={}; dimension={})".format(i.start, self.dimension))
				if i.stop >= self.dimension or i.stop < -self.dimension:
					raise IndexError("Vector slice stop out of range (stop={}; dimension={})".format(i.stop, self.dimension))
				
				if len(value) != len(list(range((len(self) + (i.start or 0)) % len(self), ((len(self) + i.stop) % len(self)) if (i.stop is not None) else len(self), i.step or 1))):
					raise ValueError("Assigned sequence must have the same length as the slice provided (expected {}, got {}).".format((len(list(range((len(self) + (i.start or 0)) % len(self), ((len(self) + i.stop) % len(self)) if (i.stop is not None) else len(self), i.step or 1)))), len(value)))
				
				if any(_v.algebra != self.algebra.base_ring for _v in value):
					raise ValueError("The assigned sequence must consist of elements of the same ring as the original vector (base_ring={}).".format(self.algebra.base_ring))
		
		self.value[i] = value
	
	def keys(self):
		yield from range(self.dimension)
	
	def values(self):
		yield from self.value
	
	def items(self):
		for key in self.keys():
			yield key, self[key]
	
	def __bool__(self):
		"Return True iff any of the elements is nonzero. Empty vector of 0 dimension gives True."
		return any(_x for _x in self)
	
	def __int__(self):
		"Encode elements of the vector as bits of an integer. The resulting value may be decoded by the constructor."
		if self.algebra.base_ring.algebra_name == 'Polynomial':
			size = self.algebra.base_ring.base_ring.size
		else:
			size = self.algebra.base_ring.size
		
		return sum((size**_n * int(_v)) for (_n, _v) in enumerate(self))
	
	def __eq__(self, other):
		try:
			return self.dimension == other.dimension and all(parallel_starmap(operator.eq, zip(self, other)))
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __add__(self, other):
		try:
			if len(self) != len(other):
				raise ValueError("Added vectors must be of the same length.")
			return self.algebra((_x + _y) for (_x, _y) in zip(self, other))
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __iadd__(self, other):
		try:
			if len(self) != len(other):
				raise ValueError("Added vectors must be of the same length.")
			for n, component in enumerate(other):
				self.value[n] += other[n]
			return self
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __sub__(self, other):
		try:
			if len(self) != len(other):
				raise ValueError("Subtracted vectors must be of the same length.")
			return self.algebra((_x - _y) for (_x, _y) in zip(self, other))
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __isub__(self, other):
		try:
			if len(self) != len(other):
				raise ValueError("Subtracted vectors must be of the same length.")
			for n, component in enumerate(other):
				self.value[n] -= other[n]
			return self
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __neg__(self):
		return self.algebra((-_x) for _x in self)
	
	def __mul__(self, other):
		"Tensor product."
		try:
			"If both arguments are vectors, return a matrix composed of the product of every component of the first vector by every component of the second vector."
			return Matrix((lambda _i, _j: self[_i] * other[_j]), column_dimension=self.dimension, row_dimension=other.dimension)
		except AttributeError:
			try:
				"Return a vector where every component of the `self` argument is multiplied on the right by the `other` factor."
				return self.algebra(list((_x * other) for _x in self), base_ring=self.algebra.base_ring)
			except TypeError:
				return NotImplemented
	
	def __rmul__(self, other):
		"Tensor product."
		try:
			"If both arguments are vectors, return a matrix composed of the product of every component of the second vector by every component of the first vector."
			return Matrix((lambda _i, _j: other[_i] * self[_j]), row_dimension=self.dimension, column_dimension=other.dimension)
		except AttributeError:
			try:
				"Return a vector where every component of the `self` argument is multiplied on the left by the `other` factor."
				return self.algebra(list((other * _x) for _x in self), base_ring=self.algebra.base_ring)
			except TypeError:
				return NotImplemented
	
	def __matmul__(self, other):
		"Scalar product of vectors or product of a vector and a scalar."
		tensor = self * other
		try:
			return tensor.trace()
		except AttributeError:
			return tensor
	
	def __rmatmul__(self, other):
		"Scalar product of vectors or product of a vector and a scalar."
		tensor = other * self
		try:
			return tensor.trace()
		except AttributeError:
			return tensor
	
	def pivot(self):
		"Position and value of the first nonzero component. Returns the vector's length and GF 0 if all components are zero."
		for n, c in enumerate(self):
			if c:
				return n, c
		else:
			return len(self), self.algebra.base_ring.zero()
	
	def canonical(self):
		return self.algebra(list(parallel_map(canonical, self)))
	
	def optimized(self):
		return self.algebra(list(parallel_map(optimized, self)))
	
	def evaluate(self):
		#return self.algebra(list(map(evaluate, self)))
		return self.algebra(list(parallel_map(evaluate, self)))
	
	def zip_vars(self, v):
		return dict(zip((str(_v) for _v in v), self))
	
	def __call__(self, **kwargs):
		return self.algebra([_el(**kwargs) for _el in self])
		#return self.algebra(list(parallel_starmap(substitute, ((_element, self.algebra.base_ring, kwargs) for _element in self))))
	
	def circuit_size(self):
		return sum(_value.circuit_size() for _value in self.values())


class Matrix(AlgebraicStructure):
	"Matrices of rings, fields or their polynomials. Mutable, but dimensions are always constant."
	
	algebra_kwparams_names = ('base_ring', 'vector_algebra')
	default_ring = BooleanRing.get_algebra()
	
	def __init__(self, init=None, column_dimension=None, row_dimension=None, base_ring=None, vector_algebra=None):
		"""
		`column_dimension` - number of columns
		`row_dimension` - number of rows
		`field_size` - if specified, check if the provided values really belong to the field of the right size; throw exception if not.
		If `init` is `None` (or not specified), create a zero matrix. `field_size` must be specified.
		If `init` is a scalar, fill the matrix with its value.
		If `init` is a list-like collection, use it as the matrix components, column-major, i.e. `init[row_dimension * col + row]`.
		If `init` is a dict-like collection, use its values indexed as `init[col, row]` as the matrix components.
		If `init` is a function, call it as `init(col, row)` to get the matrix components.
		"""
		
		try:
			column_dimension = init.column_dimension
			row_dimension = init.row_dimension
		except AttributeError:
			pass
		
		self.column_dimension = column_dimension
		self.row_dimension = row_dimension
		
		self.value = None
		
		if self.value is None:
			try:
				self.value = init.value[:]
			except AttributeError:
				pass
		
		if self.value is None:
			if init is None:
				if len(self) and (base_ring == None):
					base_ring = BooleanRing.get_algebra()
				self.value = [base_ring.zero()] * len(self)
		
		if self.value is None:
			try:
				self.value = [init[_i, _j] for (_i, _j) in self.keys()]
			except TypeError:
				pass
		
		if self.value is None:
			try:
				self.value = [init(_i, _j) for (_i, _j) in self.keys()]
			except TypeError:
				raise
		
		if self.value is None:
			try:
				self.value = list(init)
			except TypeError:
				pass
		
		if self.value is None:
			self.value = [init] * len(self)
		
		assert self.value is not None
		assert all(self[_key] == _value for (_key, _value) in zip(self.keys(), self.values()))
		assert len(self.value) == self.column_dimension * self.row_dimension
		
		if base_ring is None:
			try:
				base_ring = self.value[0].algebra
			except IndexError:
				raise ValueError("For matrix of dimension 0, 0 `base_ring` is mandatory.")
		
		if not all((_value.algebra == base_ring or not (_value.algebra == 'Polynomial' and _value.algebra.base_ring == base_ring)) for _value in self):
			raise ValueError("All components of the matrix must be from the same ring.")
		
		assert base_ring != None
		if vector_algebra == None:
			vector_algebra = Vector.get_algebra(base_ring=base_ring)
		AlgebraicStructure.__init__(self, base_ring=base_ring, vector_algebra=vector_algebra)
	
	@classmethod
	def get_algebra(cls, *params, **kwparams):
		if 'vector_algebra' not in kwparams:
			kwparams['vector_algebra'] = Vector.get_algebra(base_ring=kwparams['base_ring'])
		return super(Matrix, cls).get_algebra(*params, **kwparams)
	
	def print_bool(self):
		for i in range(self.column_dimension):
			print(" ".join(("1" if self[i, j] else "0") for j in range(self.row_dimension)))
	
	@staticmethod
	def print_bool_parallel(*ms):
		if not ms: return
		column_dimension = ms[0].column_dimension
		row_dimension = ms[0].row_dimension
		for i in range(column_dimension):
			print("\t".join([" ".join(("X" if _m[i, j] else "·") for j in range(row_dimension)) for _m in ms]))
	
	def __bool__(self):
		return any(_x for _x in self.values())
	
	def __eq__(self, other):
		if self.column_dimension != other.column_dimension or self.row_dimension != other.row_dimension:
			return False
		
		assert frozenset(self.keys()) == frozenset(other.keys())
		
		return all(parallel_starmap(operator.eq, ((self[_key], other[_key]) for _key in self.keys())))
	
	def __str__(self):
		return "Matrix[" + ", ".join(["[" + ", ".join([str(self[_i, _j]) for _j in range(self.row_dimension)]) + "]" for _i in range(self.column_dimension)]) + "]"
	
	def __len__(self):
		return self.column_dimension * self.row_dimension
	
	def __iter__(self):
		yield from self.value
	
	def __getitem__(self, i_j):
		"""
		`matrix[i, j]` return the element (i, j) of the matrix (scalar)
		`matrix[:, j]` return the column (j) of the matrix (vector)
		`matrix[i, :]` return the row (i) of the matrix (vector)
		`matrix[...]` or `matrix[:, :]` return a copy of the matrix
		`matrix[i_start:i_stop:i_step, j_start:j_stop:j_step]` return a sub-matrix with the elements specified as the slices
		"""
		
		def getitem(direction, indices_i, indices_j):
			if direction == self.__direction.scalar:
				i = indices_i
				j = indices_j
				return self.value[self.row_dimension * i + j]
			elif direction == self.__direction.row:
				j = indices_j
				return self.algebra.vector_algebra(self.value[self.row_dimension * _i + j] for _i in indices_i)
			elif direction == self.__direction.column:
				i = indices_i
				return self.algebra.vector_algebra(self.value[self.row_dimension * i + _j] for _j in indices_j)
			elif direction == self.__direction.matrix:
				selection = {}
				for (m, i), (n, j) in zip(enumerate(indices_i), enumerate(indices_j)):
					selection[m, n] = i, j
				return self.algebra((lambda _m, _n: self[self.row_dimension * selection[_m, _n][0] + selection[_m, _n][1]]), row_dimension=len(indices_i), column_dimension=len(indices_j))
			elif direction == self.__direction.copy:
				return self.algebra(self)
			else:
				raise RuntimeError("Unknown direction value: `{}`".format(repr(direction)))
		
		return self.__analyze_indices(i_j, getitem)
	
	def __setitem__(self, i_j, value):
		"""
		`matrix[i, j] = scalar` set the element (i, j) of the matrix to the scalar
		`matrix[:, j] = vector` replace the column (j) of the matrix with the vector
		`matrix[i, :] = vector` replace the row (i) of the matrix with the vector
		`matrix[...] = matrix` completely replace the matrix; the assigned value must be of the same class
		`matrix[i_start:i_stop:i_step, j_start:j_stop:j_step] = matrix` replace the sub-matrix of the elements specified as the slices with the matrix on the right-hand side
		"""
		
		def setitem(direction, indices_i, indices_j):
			if direction == self.__direction.scalar:
				i = indices_i
				j = indices_j
				self.value[self.row_dimension * i + j] = value
			elif direction == self.__direction.row:
				if len(value) != len(indices_i):
					raise ValueError("Assigned value (len {}) must have length equal to indices list ({}).".format(len(value), len(indices_i)))
				j = indices_j
				for m, i in enumerate(indices_i):
					self.value[self.row_dimension * i + j] = value[m]
			elif direction == self.__direction.column:
				if len(value) != len(indices_j):
					raise ValueError("Assigned value (len {}) must have length equal to indices list ({}).".format(len(value), len(indices_j)))
				i = indices_i
				for n, j in enumerate(indices_j):
					self.value[self.row_dimension * i + j] = value[n]
			elif direction == self.__direction.matrix:
				if self.row_dimension != len(indices_i):
					raise ValueError
				if self.column_dimension != len(indices_j):
					raise ValueError
				for (m, i), (n, j) in product(enumerate(indices_i), enumerate(indices_j)):
					self.value[self.row_dimension * i + j] = value[m, n]
			elif direction == self.__direction.copy:
				if self.__class__ != value.__class__:
					raise TypeError("In-place matrix assignment works only from a matrix of the same type.")
				if self.column_dimension != value.column_dimension or self.row_dimension != value.row_dimension:
					raise ValueError("In-place matrix assignment works only from a matrix of the same dimensions.")
				self.value = list(value.value)
			else:
				raise RuntimeError("Unknown direction value: `{}`".format(repr(direction)))
		
		self.__analyze_indices(i_j, setitem)
	
	__direction = Enum('Matrix.__direction', 'scalar row column matrix copy')
	
	def __analyze_indices(self, i_j, callback):
		if i_j == Ellipsis:
			return callback(self.__direction.copy, None, None)
		
		i, j = i_j
		
		try:
			if self.column_dimension:
				if (i.start or 0) >= 2 * self.column_dimension: raise IndexError("Start value of a slice too big. ({} vs. {})".format(i.start, 2 * self.column_dimension))
				if (i.start or 0) < -self.column_dimension: raise IndexError("Start value of a slice too low. ({} vs. {})".format(i.start, -self.column_dimension))
				if (i.stop or self.column_dimension) >= 2 * self.column_dimension: raise IndexError("Stop value of a slice too big. ({} vs. {})".format(i.stop, 2 * self.column_dimension))
				#if (i.stop or self.column_dimension) < -self.column_dimension: raise IndexError("Stop value of a slice too low. ({} vs. {})".format(i.stop, -self.column_dimension))
				
				if i.start == None:
					i_start = 0
				elif i.start < 0:
					i_start = self.column_dimension + i.start
				else:
					i_start = i.start
				
				if i.stop == None:
					i_stop = self.column_dimension
				elif i.stop < -self.column_dimension:
					i_stop = i_start
				elif i.stop < 0:
					i_stop = self.column_dimension + i.stop
				else:
					i_stop = i.stop
				
				if i_start >= self.column_dimension:
					i_start = i_stop
				
				assert i_start >= 0
				assert i_stop >= 0
				
				i_step = i.step if (i.step != None) else 1
			else:
				if i.start != None: raise IndexError("For a 0-dimensional matrix, only empty slices are allowed.")
				if i.stop != None: raise IndexError("For a 0-dimensional matrix, only empty slices are allowed.")
				if i.step != None: raise IndexError("For a 0-dimensional matrix, only empty slices are allowed.")
				
				i_start = 0
				i_stop = 0
				i_step = 1
			
			i_collection = True
		except AttributeError:
			if self.column_dimension:
				if i >= 2 * self.column_dimension: raise IndexError("Index too big. ({} vs. {})".format(i, 2 * self.column_dimension))
				if i < -self.column_dimension: raise IndexError("Index too low. ({} vs. {})".format(i, -self.column_dimension))
			
			if i < 0:
				i_start = self.column_dimension + i
			else:
				i_start = i
			
			if i < 0:
				i_stop = self.column_dimension + i + 1
			else:
				i_stop = i + 1
			
			i_step = 0
			
			assert i_start != None
			i_collection = False
		
		try:
			if i_start > i_stop and i_step >= 0:
				raise IndexError("If start index is greater than stop, step must be negative. (got: {}:{}:{})".format(i_start, i_stop, i_step))
		except TypeError:
			pass
		
		try:
			if self.row_dimension:
				if (j.start or 0) >= 2 * self.row_dimension: raise IndexError("Start value of a slice too big. ({} vs. {})".format(i.start, 2 * self.row_dimension))
				if (j.start or 0) < -self.row_dimension: raise IndexError("Start value of a slice too low. ({} vs. {})".format(i.start, -self.row_dimension))
				if (j.stop or self.row_dimension) >= 2 * self.row_dimension: raise IndexError("Stop value of a slice too big. ({} vs. {})".format(j.stop, 2 * self.row_dimension))
				#if (j.stop or self.row_dimension) < -self.row_dimension: raise IndexError("Stop value of a slice too low. ({} vs. {})".format(j.stop, -self.row_dimension))
				
				if j.start == None:
					j_start = 0
				elif j.start < 0:
					j_start = self.row_dimension + j.start
				else:
					j_start = j.start
				
				if j.stop == None:
					j_stop = self.row_dimension
				elif j.stop < -self.row_dimension:
					j_stop = j_start
				elif j.stop < 0:
					j_stop = self.row_dimension + j.stop
				else:
					j_stop = j.stop
				
				if j_start >= self.row_dimension:
					j_start = j_stop
				
				assert i_start >= 0
				assert i_stop >= 0
				
				j_step = j.step if (j.step != None) else 1
			else:
				if j.start != None: raise IndexError("For a 0-dimensional matrix, only empty slices are allowed.")
				if j.stop != None: raise IndexError("For a 0-dimensional matrix, only empty slices are allowed.")
				if j.step != None: raise IndexError("For a 0-dimensional matrix, only empty slices are allowed.")
				
				j_start = 0
				j_stop = 0
				j_step = 1
			
			j_collection = True
		except AttributeError:
			if self.row_dimension:
				if j >= 2 * self.row_dimension: raise IndexError("Index too big. ({} vs. {})".format(j, 2 * self.row_dimension))
				if j < -self.row_dimension: raise IndexError("Index too low. ({} vs. {})".format(j, -self.row_dimension))
			
			if j < 0:
				j_start = self.row_dimension + j
			else:
				j_start = j
			
			if j < 0:
				j_stop = self.row_dimension + j + 1
			else:
				j_stop = j + 1
			
			j_step = 0
			
			assert j_start != None
			j_collection = False
		
		try:
			if j_start > j_stop and j_step >= 0:
				raise IndexError("If start index is greater than stop, step must be negative. (Got: {}:{}:{})".format(j_start, j_stop, j_step))
		except TypeError:
			pass
		
		if i_collection and j_collection:
			column_dimension = len(list(range(j_start, j_stop, j_step)))
			if column_dimension > self.column_dimension:
				raise IndexError("Slice in first index too large: ({}:{}:{}) vs. {}".format(j_start, j_stop, j_step, self.column_dimension))
			row_dimension = len(list(range(i_start, i_stop, i_step)))
			if row_dimension > self.row_dimension:
				raise IndexError("Slice in first index too large: ({}:{}:{}) vs. {}".format(i_start, i_stop, i_step, self.row_dimension))
			return callback(self.__direction.matrix, list(range(i_start, i_stop, i_step)), list(range(j_start, j_stop, j_step)))
		elif i_collection:
			assert not j_collection
			assert j_start != None
			return callback(self.__direction.row, list(range(i_start, i_stop, i_step)), j_start)
		elif j_collection:
			assert not i_collection
			assert i_start != None
			return callback(self.__direction.column, i_start, list(range(j_start, j_stop, j_step)))
		else:
			return callback(self.__direction.scalar, i_start, j_start)
	
	def keys(self):
		yield from product(range(self.column_dimension), range(self.row_dimension))
	
	def values(self):
		yield from self.value
	
	def items(self):
		for key in self.keys():
			yield key, self[key]
	
	@classmethod
	def zero(cls, column_dimension, row_dimension, base_ring=default_ring, vector_algebra=None):
		"Zero matrix."
		return cls(column_dimension=column_dimension, row_dimension=row_dimension, base_ring=base_ring, vector_algebra=vector_algebra)
	
	@classmethod
	def unit(cls, dimension, base_ring=default_ring, vector_algebra=None):
		"Unit matrix."
		return cls(init=(lambda _i, _j: base_ring(_i == _j)), column_dimension=dimension, row_dimension=dimension, base_ring=base_ring, vector_algebra=vector_algebra)
	
	@classmethod
	def diagonal(cls, elements, base_ring=default_ring, vector_algebra=None):
		"Diagonal matrix; elements specified in the iterable."
		return cls(init=(lambda _i, _j: elements[_i] if _i == _j else base_ring.zero()), column_dimension=len(elements), row_dimension=len(elements), base_ring=base_ring, vector_algebra=vector_algebra)
	
	@classmethod
	def random(cls, column_dimension, row_dimension, base_ring=default_ring, vector_algebra=None):
		"Random matrix."
		return cls(init=(lambda _i, _j: base_ring.random()), column_dimension=column_dimension, row_dimension=row_dimension, base_ring=base_ring, vector_algebra=vector_algebra)
	
	@classmethod
	def random_upper_triangular_pair(cls, dimension, base_ring=default_ring, vector_algebra=None):
		"""
		Generate a pair of random upper triangular matrices that are their respective inverses.
		https://mobiusfunction.wordpress.com/2010/12/08/the-inverse-of-triangular-matrix-as-a-binomial-series/
		"""
		
		straight = cls(init=(lambda _i, _j: base_ring.random() if _i < _j else base_ring.one() if _i == _j else base_ring.zero()), column_dimension=dimension, row_dimension=dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		
		strict = straight - cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		inverse = cls.zero(dimension, dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		power = cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		
		sign = base_ring.one()
		while power:
			inverse += sign * power
			power @= strict # This sequence will converge to zero after few steps. Better algorithm needed for fields of size > 2.
			sign = -sign
		
		del power, strict
		
		#assert straight @ inverse == inverse @ straight == cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		return straight, inverse
	
	@classmethod
	def random_lower_triangular_pair(cls, dimension, base_ring=default_ring, vector_algebra=None):
		"""
		Generate a pair of random lower triangular matrices that are their respective inverses.
		https://mobiusfunction.wordpress.com/2010/12/08/the-inverse-of-triangular-matrix-as-a-binomial-series/
		"""
		
		straight = cls(init=(lambda _i, _j: base_ring.random() if _i > _j else base_ring.one() if _i == _j else base_ring.zero()), column_dimension=dimension, row_dimension=dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		
		strict = straight - cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		inverse = cls.zero(dimension, dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		power = cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		
		sign = base_ring.one()
		while power:
			inverse += sign * power
			power @= strict # This sequence will converge to zero after few steps. Better algorithm needed for fields of size > 2.
			sign = -sign
		
		del power, strict
		
		#assert straight @ inverse == inverse @ straight == cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		return straight, inverse
	
	@classmethod
	def random_permutation_pair(cls, dimension, base_ring=default_ring, vector_algebra=None):
		"Generate a pair of random permutation matrices that are their respective inverses."
		
		straight = cls.zero(dimension, dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		
		permutation = list(random_permutation(dimension))
		
		for i in range(dimension):
			j = permutation[i]
			straight[i, j] = base_ring.one()
		
		inverse = straight.transposed()
		
		#assert straight @ inverse == inverse @ straight == cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		return straight, inverse
	
	@classmethod
	def random_variable_cycle_pair(cls, dimension, value, cycle_length=None, base_ring=default_ring, vector_algebra=None):
		#if base_ring.size != 2:
		#	raise NotImplementedError("Not implemented for ring size != 2.")
		
		if dimension <= 1 and (cycle_length is not None):
			raise ValueError("For dimension <= 1 cycle_length must be None.")
		elif (cycle_length is not None) and not (2 <= cycle_length < dimension):
			raise ValueError("Cycle length (got {}) must be between 2 and matrix dimension ({}).".format(cycle_length, dimension))
		
		straight = cls.zero(dimension, dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		
		if dimension <= 1:
			return straight, straight
		elif dimension == 2:
			assert cycle_length == 2
			cycle = [0, 1]
		elif cycle_length is None:
			cycle = list(random_sample(iter(range(dimension)), dimension, randbelow(dimension - 2) + 2))
		else:
			cycle = list(random_sample(iter(range(dimension)), dimension, cycle_length))
			assert len(cycle) == cycle_length
		
		assert len(cycle) >= 2
		
		for i in range(dimension):
			if i in cycle:
				n = cycle.index(i)
				j = cycle[(n + 1) % len(cycle)]
				assert i != j
				straight[i, j] = base_ring.one() - value
				straight[i, i] = value
			else:
				straight[i, i] = base_ring.one()
		
		inverse = straight.transposed()
		
		assert straight @ inverse == inverse @ straight == cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		return straight, inverse
	
	@classmethod
	def random_invertible_diagonal_pair(cls, dimension, base_ring=default_ring, vector_algebra=None):
		"Return a pair of random diagonal matrices that are their respective inverses. For field_size==2 this is always a unit matrix."
		
		straight = cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		inverse = cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		
		if (not __debug__) and (base_ring.size == 2):
			return straight, inverse
		
		for i in range(dimension):
			while True:
				m = base_ring.random_nonzero()
				try:
					n = m**-1
				except ArithmeticError:
					continue # retry until an invertible element is found
				break
			assert m * n == base_ring.one()
			straight[i, i] = m
			inverse[i, i] = n
		
		#assert straight @ inverse == inverse @ straight == cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		return straight, inverse
	
	@classmethod
	def random_inverse_pair(cls, dimension, base_ring=default_ring, vector_algebra=None):
		"Generate a pair of random matrices that are their respective inverses."
		
		lower_triangular_straight, lower_triangular_inverse = cls.random_lower_triangular_pair(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		upper_triangular_straight, upper_triangular_inverse = cls.random_upper_triangular_pair(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		permutation_straight, permutation_inverse = cls.random_permutation_pair(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		diagonal_straight, diagonal_inverse = cls.random_invertible_diagonal_pair(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		
		result_straight =  lower_triangular_straight @ diagonal_straight @ permutation_straight @ upper_triangular_straight
		result_inverse = upper_triangular_inverse @ permutation_inverse @ diagonal_inverse @ lower_triangular_inverse
		
		#assert result_straight @ result_inverse == result_inverse @ result_straight == cls.unit(dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		return result_straight, result_inverse
	
	@classmethod
	def random_diagonal(cls, dimension, rank, base_ring=default_ring, vector_algebra=None):
		"Generate a random diagonal matrix of the specified rank."
		sample = list(random_sample(iter(range(dimension)), dimension, rank))
		assert len(sample) == rank, "{} != {}".format(len(sample), rank)
		return cls(init=(lambda _i, _j: (base_ring.random_nonzero() if ((_i == _j) and (_i in sample)) else base_ring.zero())), column_dimension=dimension, row_dimension=dimension, base_ring=base_ring, vector_algebra=vector_algebra)
	
	@classmethod
	def random_rank(cls, dimension, rank, base_ring=default_ring, vector_algebra=None):
		"Generate a random square matrix of the specified rank."
		u = cls.random(dimension, dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		v = cls.random(dimension, dimension, base_ring=base_ring, vector_algebra=vector_algebra)
		for n in range(dimension):
			if u[n, n].is_zero():
				u[n, n] = base_ring.random_nonzero()
			if v[n, n].is_zero():
				v[n, n] = base_ring.random_nonzero()
		d = cls.random_diagonal(dimension, rank, base_ring=base_ring, vector_algebra=vector_algebra)
		return u @ d @ v
	
	def __add__(self, other):
		if self.column_dimension != other.column_dimension:
			raise ValueError("Horizontal dimensions don't match in matrix addition.")
		if self.row_dimension != other.row_dimension:
			raise ValueError("Vertical dimensions don't match in matrix addition.")
		#if self.algebra != other.algebra:
		#	return NotImplemented
		
		assert frozenset(self.keys()) == frozenset(other.keys())
		
		return self.algebra((lambda _i, _j: self[_i, _j] + other[_i, _j]), column_dimension=self.column_dimension, row_dimension=self.row_dimension)
	
	def __sub__(self, other):
		if self.column_dimension != other.column_dimension:
			raise ValueError("Horizontal dimensions don't match in matrix subtraction.")
		if self.row_dimension != other.row_dimension:
			raise ValueError("Vertical dimensions don't match in matrix subtraction.")
		#if self.algebra != other.algebra:
		#	return NotImplemented
		
		assert frozenset(self.keys()) == frozenset(other.keys())
		
		return self.algebra((lambda _i, _j: self[_i, _j] - other[_i, _j]), column_dimension=self.column_dimension, row_dimension=self.row_dimension)
	
	def __neg__(self):
		return self.algebra((lambda _i, _j: -self[_i, _j]), column_dimension=self.column_dimension, row_dimension=self.row_dimension)
	
	def __mul__(self, other):
		"Element-wise product of the matrix by some value."
		return self.algebra((lambda _i, _j: self[_i, _j] * other), column_dimension=self.column_dimension, row_dimension=self.row_dimension)
	
	def __rmul__(self, other):
		return self.algebra((lambda _i, _j: other * self[_i, _j]), column_dimension=self.column_dimension, row_dimension=self.row_dimension)
	
	def __matmul__(self, other):
		try:
			if self.row_dimension != other.column_dimension:
				raise ValueError("Trying to multiply matrices of incompatible dimensions.")
			
			"Matrix product."
			
			return self.algebra((lambda _i, _j: sum((self[_i, _k] * other[_k, _j] for _k in range(self.row_dimension)), self.algebra.base_ring.zero())), column_dimension=self.column_dimension, row_dimension=other.row_dimension)
		except AttributeError:
			if self.row_dimension != other.dimension:
				raise ValueError("Trying to multiply a matrix through a vector of incompatible dimension.")
			
			"Linear transformation of a vector."
			
			return self.algebra.vector_algebra(sum((self[_i, _k] * other[_k] for _k in range(self.row_dimension)), self.algebra.base_ring.zero()) for _i in range(self.column_dimension))
		
		# TODO: multiplication by scalar
	
	def sort_rows(self, *matrices):
		for m in matrices:
			if m.column_dimension != self.column_dimension:
				raise ValueError("All matrices supplied must have the same `column_dimension` as the subject matrix.")
		
		order = [_r[0] for _r in sorted(((_n, self[_n, :].pivot()[0]) for _n in range(self.column_dimension)), key=(lambda _k: _k[1]))]
		rows = [[] for _i in range(len(matrices) + 1)]
		for r in order:
			for row, m in zip(rows, (self,) + matrices):
				row.append(m[r, :])
		
		results = [self.algebra((lambda _i, _j: _row[_i][_j]), column_dimension=self.column_dimension, row_dimension=_m.row_dimension) for (_row, _m) in zip(rows, (self,) + matrices)]
		for n, m in enumerate(matrices):
			m[...] = results[n + 1]
		
		assert results[0].column_dimension == self.column_dimension
		assert results[0].row_dimension == self.row_dimension
		return results[0]
	
	def cancel_rows(self, *matrices):
		for m in matrices:
			if m.column_dimension != self.column_dimension:
				raise ValueError("All matrices supplied must have the same `column_dimension` as the subject matrix.")
		
		rows = [[] for _i in range(len(matrices) + 1)]
		
		for n in range(self.column_dimension - 1):
			p1, c1 = self[n, :].pivot()
			p2, c2 = self[n + 1, :].pivot()
			
			if p1 == p2:
				for row, m in zip(rows, (self,) + matrices):
					row.append(m[n, :] * c2 - m[n + 1, :] * c1)
			else:
				for row, m in zip(rows, (self,) + matrices):
					row.append(m[n, :])
		
		for row, m in zip(rows, (self,) + matrices):
			v = m[-1, :]
			row.append(v)
			#print(v.dimension, m.column_dimension, m.row_dimension)
			assert v.dimension == m.row_dimension
		
		results = [self.algebra((lambda _i, _j: _row[_i][_j]), column_dimension=self.column_dimension, row_dimension=_m.row_dimension) for (_row, _m) in zip(rows, (self,) + matrices)]
		for n, m in enumerate(matrices):
			m[...] = results[n + 1]
		
		assert results[0].column_dimension == self.column_dimension
		assert results[0].row_dimension == self.row_dimension
		return results[0]
	
	def cancel_pivots(self, *matrices):
		for m in matrices:
			if m.column_dimension != self.column_dimension:
				raise ValueError("All matrices supplied must have the same `column_dimension` as the subject matrix.")
		
		s = self.algebra(self)
		
		for n in range(self.column_dimension):
			p, c = self[n, :].pivot()
			
			if not (c.is_zero() or c.is_one()):
				for m in (s,) + matrices:
					m[n, :] *= c**-1
		
		return s
	
	def is_echelon(self):
		"Check if the provided matrix is in echelon form."
		s = []
		z = []
		for n in range(self.column_dimension):
			p, c = self[n, :].pivot()
			s.append(p)
			z.append(c)
		sc = Counter(s)
		del sc[self.column_dimension]
		return all(_v == 1 for _v in sc.values()), all(_v.is_zero() or _v.is_one() for _v in z), s == sorted(s)
	
	def echelon(self, *matrices):
		"""
		Transform the matrix `self` to echelon form. The matrices in the arguments are modified in-place with the same linear operations.
		The method returns the echelon form of the `self` matrix. The original matrix is not modified unless it was provided as one of
		the arguments.
		Usage:
		 e = m.echelon()    # Return echelon form of the matrix `m` and assign it to `e`. The matrix `m` is not modified.
		 m.echelon(m)       # Modify matrix `m` to the echelon form in-place.
		 m.echelon(p, q, r) # Apply linear transformations that would turn `m` into echelon form to matrices `p`, `q`, `r`.
		"""
		
		m = self
		while not all(m.is_echelon()):
			if not m.is_echelon()[2]:
				m = m.sort_rows(*matrices)
			if __debug__: l = 0
			while not m.is_echelon()[0]:
				m = m.cancel_rows(*matrices)
				m = m.sort_rows(*matrices)
				assert l < (self.column_dimension * self.row_dimension) ** 2
				if __debug__: l += 1
			if not m.is_echelon()[1]:
				m = m.cancel_pivots(*matrices)
		return m
	
	def transposed(self):
		return self.algebra((lambda _i, _j: self[_j, _i]), column_dimension=self.row_dimension, row_dimension=self.column_dimension)
	
	def trace(self):
		if self.column_dimension != self.row_dimension:
			raise ValueError("Only square matrices have a trace.")
		
		return sum((self[_i, _i] for _i in range(self.column_dimension)), self.algebra.base_ring.zero())
	
	def diagonal_vector(self):
		"Return the matrix diagonal as a vector."
		
		if self.column_dimension != self.row_dimension:
			raise ValueError("Only square matrices have a diagonal.")
		
		return self.algebra.vector_algebra(list(self[_i, _i] for _i in range(self.column_dimension)))
	
	def canonical(self):
		return self.algebra(dict(zip(self.keys(), parallel_map(canonical, self.values()))), column_dimension=self.column_dimension, row_dimension=self.row_dimension)
	
	def optimized(self):
		return self.algebra(dict(zip(self.keys(), parallel_map(optimized, self.values()))), column_dimension=self.column_dimension, row_dimension=self.row_dimension)
	
	def evaluate(self):
		return self.algebra(dict(zip(self.keys(), parallel_map(evaluate, self.values()))), column_dimension=self.column_dimension, row_dimension=self.row_dimension)
	
	def iter_rows(self):
		for n in range(self.column_dimension):
			yield self[n, :]
	
	def iter_columns(self):
		for n in range(self.row_dimension):
			yield self[:, n]
	
	def inverse(self):
		if self.row_dimension != self.column_dimension:
			raise ValueError("Matrix is not square.")
		
		dimension = self.row_dimension
		
		rowop = self.algebra.unit(dimension)
		triangular = self.echelon(rowop)
		# TODO: raise DivisionByZeroError if the matrix is  not full rank.
		
		assert rowop @ self == triangular
		
		strict = triangular - self.algebra.unit(dimension)
		inverse = self.algebra.zero(dimension, dimension)
		power = self.algebra.unit(dimension)
		
		sign = self.algebra.base_ring.one()
		while power:
			inverse += sign * power
			power @= strict # This sequence will converge to zero after few steps. Better algorithm needed for fields of size > 2.
			sign = -sign
		
		assert inverse @ triangular == self.algebra.unit(dimension)
		assert inverse @ rowop @ self == self.algebra.unit(dimension)
		
		del power, strict, triangular
		
		return inverse @ rowop
	
	def circuit_size(self):
		return sum(_value.circuit_size() for _value in self.values())



if __debug__:
	import pickle
	from rings import *
	from polynomial import *
	from utils import parallel
	
	def test_vector(Vector):
		"Test suite for vectors."
		
		Ring = Vector.base_ring
		
		p1 = Vector.random(8)
		assert p1[...] == p1
		
		p2 = pickle.loads(pickle.dumps(p1))
		#print(p1, p2)
		assert p1 == p2
		
		p3 = p1[1:-1:2] # 1, 3, 5
		assert len(p3) == 3
		assert p3[0] == p1[1]
		assert p3[1] == p1[3]
		assert p3[2] == p1[5]
		
		a = Ring.random()
		b = Ring.random()
		c = Ring.random()
		p1[2:-1:2] = [a, b, c] # 2, 4, 6
		assert p1[2] == a
		assert p1[4] == b
		assert p1[6] == c
		assert p3[0] == p1[1]
		assert p3[1] == p1[3]
		assert p3[2] == p1[5]
		
		for l in range(8):
			v = Vector.zero(l)
			assert not v
			for n in range(l):
				assert v[n] == Ring.zero()
			
			
			for n in range(l):
				v = Vector.base(l, n)
				assert v[n] == Ring.one()
				for m in range(l):
					if m != n:
						assert v[m] == Ring.zero()
		
		for l in range(8):
			v = Vector.zero(8)
			i = randbelow(8)
			p = Ring.random()
			v[i] = p
			assert v[i] == p
			q = Ring.random()
			v[i] += q
			assert v[i] == p + q
		
		a = Vector.random(16)
		b = Vector.random(16)
		c = Vector(a)
		c += b
		assert c == a + b
		
		v = Vector.zero(8)
		v[1:4] = [Ring(1), Ring(2), Ring(3)]
		assert v[0] == Ring(0)
		assert v[1] == Ring(1)
		assert v[2] == Ring(2)
		assert v[3] == Ring(3)
		assert v[4] == Ring(0)
		assert v[5] == Ring(0)
		assert v[6] == Ring(0)
		assert v[7] == Ring(0)
		q = Ring.random()
		v *= q
		assert v[0] == Ring(0) * q
		assert v[1] == Ring(1) * q
		assert v[2] == Ring(2) * q
		assert v[3] == Ring(3) * q
		assert v[4] == Ring(0) * q
		assert v[5] == Ring(0) * q
		assert v[6] == Ring(0) * q
		assert v[7] == Ring(0) * q
		
		w = Vector.zero(8)
		w[...] = v
		assert w == v
	
	def test_matrix(Matrix):
		Vector = Matrix.vector_algebra
		Ring = Matrix.base_ring
		
		p = Matrix.random(8, 9)
		assert pickle.loads(pickle.dumps(p)) == p
		
		q = Matrix.random(8, 9)
		p[...] = q
		assert p == q
		
		for column_dimension in range(8):
			for row_dimension in range(8):
				m1 = Matrix.random(column_dimension, row_dimension)
				assert m1[...] == m1
				
				assert m1.column_dimension == column_dimension
				assert m1.row_dimension == row_dimension
				
				if row_dimension:
					r = randbelow(row_dimension)
					v1 = m1[:, r]
					assert len(v1) == column_dimension
					for n in range(len(v1)):
						assert v1[n] == m1[n, r]
					
					try:
						v2 = v1[2:-1:2]
						assert v2.algebra == Vector
						assert v2 == m1[2:-1:2, r]
						
						v3 = Vector.random(len(m1[1:-2:2, r]))
						m1[1:-2:2, r] = v3
						
						assert v3 == m1[1:-2:2, r]
						assert v2 == m1[2:-1:2, r]
					except IndexError as error:
						if column_dimension > 2:
							raise
				
				if column_dimension:
					r = randbelow(column_dimension)
					v1 = m1[r, :]
					assert len(v1) == row_dimension
					for n in range(len(v1)):
						assert v1[n] == m1[r, n]
					
					try:
						v2 = v1[2:-1:2]
						assert v2.algebra == Vector
						assert v2 == m1[r, 2:-1:2]
						
						v3 = Vector.random(len(m1[r, 1:-2:2]))
						m1[r, 1:-2:2] = v3
						
						assert v3 == m1[r, 1:-2:2]
						assert v2 == m1[r, 2:-1:2]
					except IndexError as error:
						if row_dimension > 2:
							raise
		
		for column_dimension in range(8):
			for row_dimension in range(8):
				m = Matrix.random(column_dimension, row_dimension)
				
				assert m.column_dimension == column_dimension
				assert m.row_dimension == row_dimension
				
				v = Vector.random(row_dimension)
				assert (m @ v).dimension == column_dimension
				
				w = Vector.random(row_dimension + 1)
				try:
					m @ w
					assert False
				except ValueError:
					pass
				
				if row_dimension:
					assert m[:, randbelow(row_dimension)].dimension == column_dimension
					assert m[:, -1].dimension == column_dimension
				if column_dimension:
					assert m[randbelow(column_dimension), :].dimension == row_dimension
					assert m[-1, :].dimension == row_dimension
		
		m1 = Matrix.random(8, 9)
		
		list(m1.iter_rows())
		list(m1.iter_columns())
		
		m2 = m1.sort_rows()
		ps = []
		p = 0
		match = False
		for row in m2.iter_rows():
			pn, c = row.pivot()
			match |= (p == pn)
			assert pn >= p
			p = pn
			ps.append(pn)
		
		m1.sort_rows(m1)
		assert m1 == m2
		
		m2 = m1.cancel_rows()
		#print(ps)
		#print(str(m1))
		#print(str(m2))
		redc = False
		for n, row in enumerate(m2.iter_rows()):
			pn, c = row.pivot()
			assert ps[n] <= pn
			redc |= (ps[n] < pn)
		
		assert match == redc
	
	def test_matrix_random_operations(Matrix):
		import time
		
		start = time.process_time()
		current = start
		prev = current
		print("  1 ", end="")
		Vector = Matrix.vector_algebra
		Ring = Matrix.base_ring
		Polynomial = globals()['Polynomial'].get_algebra(base_ring=Matrix.base_ring)
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  2 ", end="")
		ks, ki = Matrix.random_inverse_pair(8)
		kse = ks.echelon()
		ks.echelon(ks, ki)
		assert kse == ks
		ki1 = Matrix.unit(8)
		ki2 = ki.echelon(ki1)
		assert ki1 @ ki == ki2
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  3 ", end="")
		yes = Ring.one()
		no = Ring.zero()
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  4 ", end="")
		x0 = Polynomial.var('x0')
		x1 = Polynomial.var('x1')
		x2 = Polynomial.var('x2')
		x3 = Polynomial.var('x3')
		x4 = Polynomial.var('x4')
		x5 = Polynomial.var('x5')
		x6 = Polynomial.var('x6')
		x7 = Polynomial.var('x7')
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  5 ", end="")
		cs0, ci0 = Matrix.random_variable_cycle_pair(8, x0 + x4, cycle_length=5)
		cs1, ci1 = Matrix.random_variable_cycle_pair(8, x1 + x5, cycle_length=5)
		cs2, ci2 = Matrix.random_variable_cycle_pair(8, x2 + x6, cycle_length=5)
		cs3, ci3 = Matrix.random_variable_cycle_pair(8, x3 + x7, cycle_length=5)
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  6 ", end="")
		cs = cs0 @ cs1 @ cs2 @ cs3
		ci = ci3 @ ci2 @ ci1 @ ci0
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  7 ", end="")
		es, ei = Matrix.random_inverse_pair(8)
		fs, fi = Matrix.random_inverse_pair(8)
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  8 ", end="")
		cs = es @ cs @ fi
		ci = fs @ ci @ ei
		current = time.process_time()
		print(current - start, current - prev)
		prev = current

		print("  9.0 ", end="")
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		print(cs.circuit_size(), ci.circuit_size())
		
		#print("  9.1 ", end="")
		#with parallel():
		#	cs = cs.canonical()
		#	ci = ci.canonical()
		#current = time.process_time()
		#print(current - start, current - prev)
		#prev = current
		#print(cs.circuit_size(), ci.circuit_size())
		
		print("  9.5 ", end="")
		with parallel():
			cs = cs.optimized()
			ci = ci.optimized()
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		print(cs.circuit_size(), ci.circuit_size())
		
		#print(str(cs))
		#print()
		#print(str(ci))
		#print()
		
		print("  10 ", end="")
		with parallel():
			assert cs @ ci == ci @ cs == Matrix.unit(8)
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  11 ", end="")
		csA = Matrix({_key: _value(x0=no, x1=no, x2=no, x3=no, x4=no, x5=no, x6=no, x7=no).evaluate() for (_key, _value) in cs.items()}, 8, 8)
		ciA = Matrix({_key: _value(x0=no, x1=no, x2=no, x3=no, x4=no, x5=no, x6=no, x7=no).evaluate() for (_key, _value) in ci.items()}, 8, 8)
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		#csA.print_bool()
		#ciA.print_bool()
		#print()
		
		print("  12 ", end="")
		assert csA @ ciA == ciA @ csA == Matrix.unit(8)
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		print("  13 ", end="")
		csB = Matrix({_key: _value(x0=yes, x1=no, x2=no, x3=no, x4=no, x5=no, x6=no, x7=no).evaluate() for (_key, _value) in cs.items()}, 8, 8)
		ciB = Matrix({_key: _value(x0=yes, x1=no, x2=no, x3=no, x4=no, x5=no, x6=no, x7=no).evaluate() for (_key, _value) in ci.items()}, 8, 8)
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
		
		#csB.print_bool()
		#ciB.print_bool()
		#print()
		
		print("  14 ", end="")
		assert csB @ ciB == ciB @ csB == Matrix.unit(8)
		current = time.process_time()
		print(current - start, current - prev)
		prev = current

		print("  15 ", end="")
		current = time.process_time()
		print(current - start, current - prev)
		prev = current
	
	def linear_test_suite(verbose=False):
		if verbose: print("running test suite")
		
		for i in chain(range(2, 16), (2**_i for _i in range(5, 11))):
			if verbose: print()
			if verbose: print("test ModularRing(size={})".format(i))
			ring = ModularRing.get_algebra(size=i)
			if verbose: print(" vector test")
			test_vector(Vector.get_algebra(base_ring=ring))
			if verbose: print(" matrix test")
			test_matrix(Matrix.get_algebra(base_ring=ring))
			
			if i == 2:
				if verbose: print(" matrix random operations test")
				test_matrix_random_operations(Matrix.get_algebra(base_ring=ring))
			
			if i <= 256:
				if verbose: print()
				if verbose: print("test Polynomial(base_ring=ModularRing(size={}))".format(i))
				ring_polynomial = Polynomial.get_algebra(base_ring=ring)
				if verbose: print(" vector test")
				test_vector(Vector.get_algebra(base_ring=ring_polynomial))
				if verbose: print(" matrix test")
				test_matrix(Matrix.get_algebra(base_ring=ring_polynomial))
		
		if verbose: print()
		if verbose: print("test BooleanRing()")
		ring = BooleanRing.get_algebra()
		if verbose: print(" vector test")
		test_vector(Vector.get_algebra(base_ring=ring))
		if verbose: print(" matrix test")
		test_matrix(Matrix.get_algebra(base_ring=ring))
		if verbose: print(" matrix random operations test")
		test_matrix_random_operations(Matrix.get_algebra(base_ring=ring))
		
		if verbose: print()
		if verbose: print("test Polynomial(base_ring=BooleanRing())")
		ring_polynomial = Polynomial.get_algebra(base_ring=ring)
		test_polynomial(ring_polynomial)
		if verbose: print(" vector test")
		test_vector(Vector.get_algebra(base_ring=ring_polynomial))
		if verbose: print(" matrix test")
		test_matrix(Matrix.get_algebra(base_ring=ring_polynomial))
		
		for i in (2,): #(3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 18, 19, 23, 25, 32, 49, 64, 81, 121, 128, 256, 52, 1024):
			if verbose: print()
			if verbose: print("test GaloisField(size={})".format(i))
			field = GaloisField.get_algebra(size=i)
			if verbose: print(" vector test")
			test_vector(Vector.get_algebra(base_ring=field))
			if verbose: print(" matrix test")
			test_matrix(Matrix.get_algebra(base_ring=field))
			if i == 2 or i == 8 or i == 256:
				if verbose: print(" matrix random operations test")
				test_matrix_random_operations(Matrix.get_algebra(base_ring=field))
			
			if verbose: print()
			if verbose: print("test Polynomial(base_ring=GaloisField(size={}))".format(i))
			field_polynomial = Polynomial.get_algebra(base_ring=field)
			if verbose: print(" vector test")
			test_vector(Vector.get_algebra(base_ring=field_polynomial))
			if verbose: print(" matrix test")
			test_matrix(Matrix.get_algebra(base_ring=field_polynomial))
		
		assert BinaryField.get_algebra(exponent=1)(1) != RijndaelField(1)
		
		for i in (1,): #(2, 3, 4, 5, 6, 7, 8, 16, 32, 64):
			if verbose: print()
			if verbose: print("test BinaryField(exponent={})".format(i))
			field = BinaryField.get_algebra(exponent=i)
			if verbose: print(" vector test")
			test_vector(Vector.get_algebra(base_ring=field))
			if verbose: print(" matrix test")
			test_matrix(Matrix.get_algebra(base_ring=field))
			if i == 1 or i == 3 or i == 8:
				if verbose: print(" matrix random operations test")
				test_matrix_random_operations(Matrix.get_algebra(base_ring=field))
			
			if verbose: print()
			if verbose: print("test Polynomial(base_ring=BinaryField(exponent={}))".format(i))
			field_polynomial = Polynomial.get_algebra(base_ring=field)
			if verbose: print(" vector test")
			test_vector(Vector.get_algebra(base_ring=field_polynomial))
			if verbose: print(" matrix test")
			test_matrix(Matrix.get_algebra(base_ring=field_polynomial))
		
		if verbose: print()
		if verbose: print("test RijndaelField()")
		field = RijndaelField		
		if verbose: print(" vector test")
		test_vector(Vector.get_algebra(base_ring=field))
		if verbose: print(" matrix test")
		test_matrix(Matrix.get_algebra(base_ring=field))
		#if verbose: print(" matrix random operations test")
		#test_matrix_random_operations(Matrix.get_algebra(base_ring=field))
		
		if verbose: print()
		if verbose: print("test Polynomial(base_ring=RijndaelField())")
		field_polynomial = Polynomial.get_algebra(base_ring=field)
		if verbose: print(" vector test")
		test_vector(Vector.get_algebra(base_ring=field_polynomial))
		if verbose: print(" matrix test")
		test_matrix(Matrix.get_algebra(base_ring=field_polynomial))
	
	__all__ = __all__ + ('test_vector', 'test_matrix', 'test_matrix_random_operations', 'linear_test_suite',)


if __debug__ and __name__ == '__main__':
	linear_test_suite(verbose=True)



