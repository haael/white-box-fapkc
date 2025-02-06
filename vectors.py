#!/usr/bin/python3


__all__ = 'Vector', 'Matrix'


from itertools import product, chain
from typing import TypeVar, Iterable

from utils import cached, array_fallback, table_fallback


Scalar = TypeVar('Scalar')


class Vector:
	@property
	@cached
	def Field(self):
		return self[0].Field
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__values.__class__)
	
	@cached
	def zero_element(self):
		return self.Field.zero()
	
	@cached
	def one_element(self):
		return self.Field.one()
	
	@classmethod
	def random(cls, length, Array, Field, randbelow):
		nArray = array_fallback(Array)
		return cls(nArray((Field.random(randbelow) for _n in range(length)), [None], [Field]))
	
	@classmethod
	def random_nonzero(cls, length, Array, Field, randbelow):
		nArray = array_fallback(Array)
		
		values = []
		nonzero = False
		for n in range(length):
			if not nonzero and n == length - 1:
				f = Field.random_nonzero(randbelow)
			else:
				f = Field.random(randbelow)
			
			if f:
				nonzero = True
			
			values.append(f)
		
		return cls(nArray(values, [None], [Field]))
	
	@classmethod
	def zero(cls, length, Array, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Field.zero() for _n in range(length)), [None], [Field]))
	
	def __init__(self, values):
		try:
			self.__values = values.__values
			self.vector_length = values.vector_length
		except AttributeError:
			pass
		else:
			return
		
		self.__values = values
		self.vector_length = len(values)
	
	def __getnewargs__(self):
		return self.__values,
	
	def serialize(self) -> Iterable[int]:
		try:
			return self.__values.serialize()
		except AttributeError:
			return self.__values
	
	@classmethod
	def deserialize(cls, length, Array, Field, data):
		nArray = array_fallback(Array)
		return cls(nArray((Field.deserialize(data) for _n in range(length)), [None], [Field]))
	
	def __repr__(self) -> str:
		return f'{self.__class__.__name__}({{{ ", ".join(str(_n) + ": " + str(self.__values[_n]) for _n in self.keys()) }}})'
	
	def __str__(self) -> str:
		return "Vector[" + ", ".join([str(_v) for _v in self.__values]) + "]"
	
	def __len__(self) -> int:
		return self.vector_length
	
	def keys(self):
		yield from range(len(self))
	
	def values(self):
		yield from self.__values
	
	def items(self):
		yield from enumerate(self.__values)
	
	def __getitem__(self, index:int) -> Scalar:
		if index is Ellipsis:
			return self.__class__(self.Array(iter(self), [None], [self.Field]))
		elif hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step'):
			return self.__class__(self.__values[index])
		else:
			return self.__values[index]
	
	def __setitem__(self, index:int, value:Scalar) -> None:
		if index is Ellipsis or (hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step')):
			if hasattr(value, '_Vector__values'):
				self.__values[index] = value.__values
			else:
				self.__values[index] = value
		else:
			self.__values[index] = value
	
	def __eq__(self, other) -> bool:
		try:
			return len(self) == len(other) and all(self[_n] == other[_n] for _n in self.keys())
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __or__(self, other):
		return self.__class__(self.Array(chain(self, other), [None], [self.Field]))
	
	def __ror__(self, other):
		return self.__class__(self.Array(chain(other, self), [None], [self.Field]))
	
	def __add__(self, other):
		if hasattr(other, 'vector_length'):
			if self.vector_length != other.vector_length:
				raise ValueError(f"Vector lengths don't match ({self.vector_length} vs. {other.vector_length}).")
			return self.__class__(self.Array((self[_n] + other[_n] for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented
	
	def __sub__(self, other):
		if hasattr(other, 'vector_length'):
			if self.vector_length != other.vector_length:
				raise ValueError(f"Vector lengths don't match ({self.vector_length} vs. {other.vector_length}).")
			return self.__class__(self.Array((self[_n] - other[_n] for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented
	
	def __pos__(self):
		return self
	
	def __neg__(self):
		return self.__class__(self.Array((-self[_n] for _n in self.keys()), [None], [self.Field]))
	
	def __mul__(self, other):
		try:
			return self.__class__(self.Array((self[_n] * other for _n in self.keys()), [None], [self.Field]))
		except TypeError:
			return NotImplemented
	
	def __rmul__(self, other):
		try:
			return self.__class__(self.Array((other * self[_n] for _n in self.keys()), [None], [self.Field]))
		except TypeError:
			return NotImplemented
	
	def __matmul__(self, other):
		if hasattr(other, 'vector_length'):
			if self.vector_length != other.vector_length:
				raise ValueError("Vector lengths don't match.")
			return self.Field.sum(self[_n] @ other[_n] for _n in self.keys())
		elif hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__(self.Array((self[_n] @ other for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented
	
	def __rmatmul__(self, other):
		if hasattr(other, 'vector_length'):
			if self.vector_length != other.vector_length:
				raise ValueError("Vector lengths don't match.")
			return self.Field.sum(other[_n] @ self[_n] for _n in self.keys())
		elif hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__(self.Array((other @ self[_n] for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented


class Matrix:
	@property
	@cached
	def Field(self):
		return self[0, 0].Field
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__values.__class__)
	
	@property
	@cached
	def Table(self):
		return table_fallback(self.__values.__class__)
	
	@cached
	def zero_element(self):
		return self.Field.zero()
	
	@cached
	def one_element(self):
		return self.Field.one()
	
	@classmethod
	def random(cls, height, width, Table, Array, Field, randbelow):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), Field.random(randbelow)) for (_m, _n) in product(range(height), range(width))), [height, width], [None], [Field], Array=Array))
	
	@classmethod
	def zero(cls, height, width, Table, Array, Field):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), Field.zero()) for (_m, _n) in product(range(height), range(width))), [height, width], [None], [Field], Array=Array))
	
	@classmethod
	def one(cls, height, width, Table, Array, Field):
		if height != width:
			raise ValueError("Unit matrix height must be equal to width.")
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), (Field.one() if _m == _n else Field.zero())) for (_m, _n) in product(range(height), range(width))), [height, width], [None], [Field], Array=Array))
	
	ident = one
	
	def __init__(self, values):
		try:
			self.__values = values.__values
			self.matrix_height = values.matrix_height
			self.matrix_width = values.matrix_width
		except AttributeError:
			pass
		else:
			return
		
		width = 0
		height = 0
		for m, n in values.keys():
			if m >= height:
				height = m + 1
			if n >= width:
				width = n + 1
		
		self.__values = values
		self.matrix_height = height
		self.matrix_width = width
	
	def __bool__(self) -> bool:
		return any(self.values())
	
	def __str__(self) -> str:
		return 'Matrix[' + ', '.join('[' + ', '.join(str(self[_m, _n]) for _n in range(self.matrix_width)) + ']' for _m in range(self.matrix_height)) + ']'
	
	def keys(self):
		yield from product(range(self.matrix_height), range(self.matrix_width))
	
	def values(self):
		yield from self.__values.values()
	
	def items(self):
		yield from self.__values.items()
	
	def __getitem__(self, index:tuple[int, int]) -> Scalar:
		try:
			m, n = index
		except ValueError:
			raise IndexError("Matrix index must be a 2-tuple.")
		
		if not 0 <= m < self.matrix_height:
			raise IndexError(f"Matrix vertical index {m} out of bounds [0, {self.matrix_height}).")
		
		if not 0 <= n < self.matrix_width:
			raise IndexError(f"Matrix vertical index {n} out of bounds [0, {self.matrix_width}).")
		
		return self.__values[m, n]
	
	def __setitem__(self, index:tuple[int, int], value:Scalar) -> None:
		try:
			m, n = index
		except ValueError:
			raise IndexError("Matrix index must be a 2-tuple.")
		
		if not 0 <= m < self.matrix_height:
			raise IndexError(f"Matrix vertical index {m} out of bounds [0, {self.matrix_height}).")
		
		if not 0 <= n < self.matrix_width:
			raise IndexError(f"Matrix vertical index {n} out of bounds [0, {self.matrix_width}).")
		
		self.__values[m, n] = value
	
	def __eq__(self, other) -> bool:
		try:
			return self.matrix_width == other.matrix_width and self.matrix_height == other.matrix_height and all(self[_m, _n] == other[_m, _n] for (_m, _n) in self.keys())
		except (IndexError, AttributeError):
			return NotImplemented
	
	def __add__(self, other):
		if hasattr(other, 'matrix_width') and hasattr(other, 'matrix_height'):
			if not (self.matrix_width == other.matrix_width and self.matrix_height == other.matrix_height):
				raise ValueError("Matrix dimensions don't match.")
			return self.__class__(self.Table((((_m, _n), self[_m, _n] + other[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		else:
			return NotImplemented
	
	def __sub__(self, other):
		if hasattr(other, 'matrix_width') and hasattr(other, 'matrix_height'):
			if not (self.matrix_width == other.matrix_width and self.matrix_height == other.matrix_height):
				raise ValueError("Matrix dimensions don't match.")
			return self.__class__(self.Table((((_m, _n), self[_m, _n] - other[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		else:
			return NotImplemented
	
	def __neg__(self):
		return self.__class__(self.Table((((_m, _n), -self[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
	
	def __mul__(self, other):
		return self.__class__(self.Table((((_m, _n), self[_m, _n] * other) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
	
	def __rmul__(self, other):
		return self.__class__(self.Table((((_m, _n), other * self[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
	
	def __matmul__(self, other):
		if hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying matrix by a scalar from a different field.")
			return self.__class__(self.Table((((_m, _n), self[_m, _n] @ other) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		elif hasattr(other, 'vector_length'):
			if self.matrix_width != other.vector_length:
				raise ValueError("Matrix width does not equal vector length.")
			return other.__class__(other.Array((self.Field.sum(self[_m, _n] @ other[_n] for _n in range(self.matrix_width)) for _m in range(self.matrix_height)), [None], [self.Field]))
		elif hasattr(other, 'matrix_width') and hasattr(other, 'matrix_height'):
			if self.matrix_width != other.matrix_height:
				raise ValueError("Left matrix height does not equal right matrix width.")
			return self.__class__(self.Table((((_m, _n), self.Field.sum(self[_m, _k] @ other[_k, _n] for _k in range(self.matrix_width))) for (_m, _n) in product(range(self.matrix_height), range(other.matrix_width))), [self.matrix_height, other.matrix_width], [None], [self.Field], Array=self.Array))
		else:
			return NotImplemented
	
	def __rmatmul__(self, other):
		"When math-multiplying a vector on the left by a matrix on the right, the result is an action of a transposed matrix on the vector. Element multiplications are taken in reverse order."
		
		if hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying matrix by a scalar from a different field.")
			return self.__class__(self.Table((((_m, _n), other @ self[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		elif hasattr(other, 'vector_length'):
			if self.matrix_height != other.vector_length:
				raise ValueError("Matrix height does not equal vector length.")
			return other.__class__(other.Array((self.Field.sum(other[_m] @ self[_m, _n] for _m in range(self.matrix_height)) for _n in range(self.matrix_width)), [None], [self.Field]))
		elif hasattr(other, 'matrix_width') and hasattr(other, 'matrix_height'):
			if self.matrix_height != other.matrix_width:
				raise ValueError("Left matrix height does not equal right matrix width.")
			return self.__class__(self.Table((((_m, _n), self.Field.sum(other[_m, _k] @ self[_k, _n] for _k in range(other.matrix_width))) for (_m, _n) in product(range(other.matrix_height), range(self.matrix_width))), [other.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		else:
			return NotImplemented
	
	def transpose(self):
		return self.__class__(self.Table((((_n, _m), self[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_width, self.matrix_height], [None], [self.Field], Array=self.Array))
	
	def inverse(self):
		if self.matrix_width != self.matrix_height:
			raise ValueError
		
		l, u, perm = self.__ldup()
		
		while True:
			try:
				L_less_1 = self.__class__(self.Table((((i, j), self.zero_element() if i == j else l(i, j)) for (i, j) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
				D_inv = self.__class__(self.Table((((i, j), u(i, j)**-1 if i == j else self.zero_element()) for (i, j) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
				U_less_1 = self.__class__(self.Table((((i, j), self.zero_element() if i == j else u(i, j) @ u(i, i)**-1) for (i, j) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
				P_inv = self.__class__(self.Table((((i, j), self.one_element() if perm[i] == j else self.zero_element()) for (i, j) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
				break
			
			except self.__PermutationNeeded as pn:
				pn.advance()
		
		# https://mobiusfunction.wordpress.com/2010/12/08/the-inverse-of-triangular-matrix-as-a-binomial-series/
		
		L_inv = self.zero(self.matrix_height, self.matrix_width, self, self, self.Field)
		L_pow = self.one(self.matrix_height, self.matrix_width, self, self, self.Field)
		F_sgn = self.one_element()
		while L_pow: # will converge to 0
			L_inv += F_sgn @ L_pow
			L_pow @= L_less_1
			F_sgn = -F_sgn
		
		U_inv = self.zero(self.matrix_height, self.matrix_width, self, self, self.Field)
		U_pow = self.one(self.matrix_height, self.matrix_width, self, self, self.Field)
		F_sgn = self.one_element()
		while U_pow: # will converge to 0
			U_inv += F_sgn @ U_pow
			U_pow @= U_less_1
			F_sgn = -F_sgn
		
		return U_inv @ D_inv @ L_inv @ P_inv
	
	def __pow__(self, n:int):
		result = self.one(self.matrix_height, self.matrix_width, self, self, self.Field)
		if n > 0:
			for i in range(n):
				result @= self
		elif n < 0:
			inv = self.inverse()
			for i in range(abs(n)):
				result @= inv
		return result
	
	class __PermutationNeeded(BaseException):
		def __init__(self, row, perm, avoid, mat, l, u):
			self.row = row
			self.perm = perm
			self.avoid = avoid
			self.mat = mat
			self.l = l
			self.u = u
		
		def advance(self):
			self.l.clear_cache()
			self.u.clear_cache()
			
			perm = self.perm
			mat = self.mat
			r = self.row
			avoid = self.avoid
			size = len(perm)
			
			k = None
			
			for kk in range(r, size):
				#print(perm[kk], r, mat[perm[kk], r], mat[perm[r], r], [mat[perm[kk], _i] for _i in range(size)])
				if mat[perm[kk], r] != mat[perm[r], r] and perm[kk] != kk:
					k = kk
					break
			else:
				k = None
			
			#if k is None:
			#	if r != 0:
			#		print("reset", r)
			#		for i in range(size):
			#			perm[i] = i
			#		k = 0
			
			#if k is None:
			#	for kk in range(1, size):
			#		k = (r + kk) % size
			#		if perm[k] == k:
			#			break
			#	else:
			#		k = None
			
			#if k is None:
			#	for kk in range(1, size):
			#		k = (r + kk) % size
			#		if mat[perm[k], k] != avoid:
			#			break
			#	else:
			#		k = None
			
			if k is None:
				#print(perm)
				raise ArithmeticError("Could not decompose.")
			
			#print(r, k)
			
			perm[r], perm[k] = perm[k], perm[r]
	
	def __ldup(self):
		if self.matrix_width != self.matrix_height:
			raise ValueError
		
		size = self.matrix_width
		perm = [_n for _n in range(size)]
		
		def cached(f):
			c = {}
			def g(i, j):
				if (i, j) in c:
					return c[i, j]
				else:
					y = f(i, j)
					c[i, j] = y
					return y
			
			def clear_cache():
				c.clear()
			g.clear_cache = clear_cache
			
			return g
		
		perm = [_n for _n in range(size)]
		
		# https://www.geeksforgeeks.org/doolittle-algorithm-lu-decomposition/
		
		@cached
		def u(i, j):
			if i > j:
				return self.zero_element()
			
			return self[perm[i], j] - self.Field.sum(l(i, k) @ u(k, j) for k in range(i))
		
		@cached
		def l(i, j):
			if i < j:
				return self.zero_element()
			
			e = self[perm[i], j] - self.Field.sum(l(i, k) @ u(k, j) for k in range(j))
			if not e:
				return e
			
			d = u(j, j)
			if not d:
				raise self.__PermutationNeeded(j, perm, self.Field.sum(l(j, k) @ u(k, j) for k in range(j)), self, l, u)
			
			return e @ d**-1
		
		return l, u, perm
	
	def ldup_decomposition(self):
		if self.matrix_width != self.matrix_height:
			raise ValueError
		size = self.matrix_width
		
		l, u, perm = self.__ldup()
		while True:
			try:
				L = self.__class__(self.Table((((i, j), self.one_element() if i == j else l(i, j)) for (i, j) in self.keys()), [size, size], [None], [self.Field], Array=self.Array))
				D = self.__class__(self.Table((((i, j), u(i, j) if i == j else self.zero_element()) for (i, j) in self.keys()), [size, size], [None], [self.Field], Array=self.Array))
				U = self.__class__(self.Table((((i, j), self.one_element() if i == j else u(i, j) @ u(i, i)**-1 if u(i, j) else self.zero_element()) for (i, j) in self.keys()), [size, size], [None], [self.Field], Array=self.Array))
				P = self.__class__(self.Table((((i, j), self.one_element() if perm[i] == j else self.zero_element()) for (i, j) in self.keys()), [size, size], [None], [self.Field], Array=self.Array))
				return L, D, U, P
			
			except self.__PermutationNeeded as pn:
				pn.advance()
	
	def determinant(self):
		if self.matrix_width != self.matrix_height:
			raise ValueError
		size = self.matrix_width
		
		l, u, perm = self.__ldup()
		
		while True:
			try:
				d = self.Field.one()
				for i in range(size):
					d *= u(i, i)
				break
			
			except self.__PermutationNeeded as pn:
				pn.advance()
		
		for m in range(size):
			for n in range(m + 1, size):
				if perm[m] > perm[n]:
					d = -d
		
		return d


if __debug__ and __name__ == '__main__':
	from fields import Galois
	from random import randrange
		
	fields = Galois('Binary', 2, [1, 1]), Galois('F3', 3, [1, 0, 2, 1]), Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])	
	
	for F in fields:
		print("Vectors over:", F)
		
		_0 = F.zero()
		_1 = F.one()
		
		print("Vector algebra test.")
		for n in range(100):
			w = n // 10 + 1
			
			_V0 = Vector.zero(w, list, F)
			
			a = Vector.random(w, list, F, randrange)
			b = Vector.random(w, list, F, randrange)
			c = Vector.random(w, list, F, randrange)
			f = F.random(randrange)
			g = F.random(randrange)
			
			assert len(a | b) == len(a) + len(b)
			assert a + b == b + a
			assert a - b == -(b - a)
			assert a + _V0 == a
			assert _V0 + a == a
			assert a - _V0 == a
			assert _V0 - a == -a
			assert _0 * a == _V0
			assert a * _0 == _V0
			assert f * (a + b) == f * a + f * b
			assert f * (a - b) == f * a - f * b
			assert a @ b == b @ a
			assert a @ (b + c) == a @ b + a @ c
			assert (a + b) @ c == a @ c + b @ c
			assert (a * f) @ b == f * (a @ b)
			assert (f * a) @ b == f * (a @ b)
			assert a @ (b * f) == f * (a @ b)
			assert a @ (f * b) == f * (a @ b), f"a={a} f={f} b={b}; {a @ (f * b)} == {f * (a @ b)}"
			assert (f * a) @ (g * b) == (f * g) * (a @ b), f"a={a} f={f} b={b} g={g}; {(f * a) @ (g * b)} == {(f * g) * (a @ b)}"
				
		print("Rectangular matrix algebra test.")
		for n in range(50):
			w = n // 7 + 1
			h = n % 7 + 1
			
			_M0 = Matrix.zero(w, h, dict, list, F)
			
			a = Matrix.random(w, h, dict, list, F, randrange)
			b = Matrix.random(w, h, dict, list, F, randrange)
			c = Matrix.random(h, w, dict, list, F, randrange)
			f = F.random(randrange)
			g = F.random(randrange)
			
			assert a + b == b + a
			assert a - b == -(b - a)
			
			assert a + _M0 == a
			assert _M0 + a == a
			assert a - _M0 == a
			assert _M0 - a == -a
			assert a * _0 == _M0
			assert _0 * a == _M0
			
			assert f * (a + b) == f * a + f * b
			assert f * (a - b) == f * a - f * b
			
			assert c @ (a + b) == c @ a + c @ b
			assert (a + b) @ c == a @ c + b @ c
			
			assert (a * f) @ c == f * (a @ c)
			assert (f * a) @ c == f * (a @ c)
			assert a @ (c * f) == f * (a @ c)
			assert a @ (f * c) == f * (a @ c)
			assert (f * a) @ (g * c) == (f * g) * (a @ c)
		
		print("Square matrix algebra test.")
		for w in range(1, 10):
			_Mid = Matrix.one(w, w, dict, list, F)
			
			a = Matrix.random(w, w, dict, list, F, randrange)
			
			assert _Mid @ a == a
			assert a @ _Mid == a
			
			while True:
				m = Matrix.random(w, w, dict, list, F, randrange) # TODO: create random nonsingular matrix
				
				try:
					l, d, u, p = m.ldup_decomposition()
				except ArithmeticError:
					continue
				
				for ii, jj in l.keys():
					assert l[ii, jj] == m.one_element() if ii == jj else True
					assert l[ii, jj] == m.zero_element() if ii < jj else True
				
				for ii, jj in d.keys():
					assert d[ii, jj] == m.zero_element() if ii != jj else True
				
				for ii, jj in u.keys():
					assert u[ii, jj] == m.one_element() if ii == jj else True
					assert u[ii, jj] == m.zero_element() if ii > jj else True
				
				assert l @ d @ u == p @ m
				
				try:
					n = m.inverse()
				except ArithmeticError:
					continue
				
				v = Vector.random_nonzero(w, list, F, randrange)
				t = m @ v
				s = n @ v
				
				assert m @ n == _Mid, f"{m} @ {n} = {m @ n}"
				assert n @ m == _Mid, f"{n} @ {m} = {n @ m}"
				
				assert m @ s == v
				assert n @ t == v
				
				break
		
		print("Vector vs. matrix operations test.")
		for h in range(1, 8):
			for w in range(1, 8):
				f1 = F.random(randrange)
				f2 = F.random(randrange)
				
				vw1 = Vector.random(w, list, F, randrange)
				vw2 = Vector.random(w, list, F, randrange)
				vh1 = Vector.random(h, list, F, randrange)
				vh2 = Vector.random(h, list, F, randrange)
				
				m1 = Matrix.random(h, w, dict, list, F, randrange)
				m2 = Matrix.random(h, w, dict, list, F, randrange)
				n1 = Matrix.random(w, h, dict, list, F, randrange)
				n2 = Matrix.random(w, h, dict, list, F, randrange)
				
				assert m1 @ (f1 + f2) == m1 @ f1 + m1 @ f2
				assert (f1 + f2) @ m2 == f1 @ m2 + f2 @ m2
				assert (m1 + m2) @ f1 == m1 @ f1 + m2 @ f1
				assert f2 @ (m1 + m2) == f2 @ m1 + f2 @ m2
				
				assert m1 @ (vw1 + vw2) == m1 @ vw1 + m1 @ vw2
				assert (vh1 + vh2) @ m2 == vh1 @ m2 + vh2 @ m2
				assert (m1 + m2) @ vw1 == m1 @ vw1 + m2 @ vw1
				assert vh2 @ (m1 + m2) == vh2 @ m1 + vh2 @ m2
				
				assert m1 @ (f1 - f2) == m1 @ f1 - m1 @ f2
				assert (f1 - f2) @ m2 == f1 @ m2 - f2 @ m2
				assert (m1 - m2) @ f1 == m1 @ f1 - m2 @ f1
				assert f2 @ (m1 - m2) == f2 @ m1 - f2 @ m2
				
				assert m1 @ (vw1 - vw2) == m1 @ vw1 - m1 @ vw2
				assert (vh1 - vh2) @ m2 == vh1 @ m2 - vh2 @ m2
				assert (m1 - m2) @ vw1 == m1 @ vw1 - m2 @ vw1
				assert vh2 @ (m1 - m2) == vh2 @ m1 - vh2 @ m2
				
				assert (m1 + m2) @ n1 == m1 @ n1 + m2 @ n1
				assert m1 @ (n1 + n2) == m1 @ n1 + m1 @ n2
				assert n2 @ (m1 + m2) == n2 @ m1 + n2 @ m2
				assert (n1 + n2) @ m2 == n1 @ m2 + n2 @ m2
				
				assert (m1 - m2) @ n1 == m1 @ n1 - m2 @ n1
				assert m1 @ (n1 - n2) == m1 @ n1 - m1 @ n2
				assert n2 @ (m1 - m2) == n2 @ m1 - n2 @ m2
				assert (n1 - n2) @ m2 == n1 @ m2 - n2 @ m2
				
				assert (m1 @ n1) @ vh1 == m1 @ (n1 @ vh1)
				assert (n2 @ m2) @ vw1 == n2 @ (m2 @ vw1)
				
				#if w == h and F.field_size != 2: # FIXME
				#	assert (m1 @ n1).determinant() == m1.determinant() * n1.determinant()
		
