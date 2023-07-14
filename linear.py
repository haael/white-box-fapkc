#!/usr/bin/python3


__all__ = 'Linear', 'Quadratic', 'Vector', 'Matrix'


from itertools import zip_longest, product, chain
from math import sqrt, ceil
from collections import defaultdict

from utils import superscript, cached


def array_fallback(Array):
	try:
		return Array.Array
	except AttributeError:
		if isinstance(Array, type):
			return lambda values, sizes, types: Array(values)
		else:
			return Array


class Linear:
	"Linear (uniform) function of single argument. `F(x + y) = F(x) + F(y); F(0) = 0`."
	
	@property
	def Field(self):
		return self.__f[0].Field
	
	@classmethod
	@property
	def Linear(cls):
		return cls
	
	@property
	def Array(self):
		return array_fallback(self.__f.__class__)
	
	@classmethod
	def zero(cls, Array, Field):
		nArray = array_fallback(Array)		
		return cls(nArray((Field(0) for _n in range(Field.field_power)), [None], [Field]))
	
	@classmethod
	def one(cls, Array, Field):
		nArray = array_fallback(Array)		
		return cls(nArray(chain([Field(1)], (Field(0) for _n in range(Field.field_power - 1))), [None], [Field]))
	
	@classmethod
	def factor(cls, value, Array):
		nArray = array_fallback(Array)		
		Field = value.__class__
		return cls(nArray(chain([value], (Field(0) for _n in range(Field.field_power - 1))), [None], [Field]))
	
	@classmethod
	def random(cls, Array, Field, randbelow):
		nArray = array_fallback(Array)		
		return cls(nArray((Field.random(randbelow) for n in range(Field.field_power)), [None], [Field]))
	
	@classmethod
	def random_nonzero(cls, Array, Field, randbelow):
		nArray = array_fallback(Array)		
		
		f = []
		nonzero = False
		for n in range(Field.field_power - 1):
			v = Field.random(randbelow)
			if v:
				nonzero = True
			f.append(v)
		
		if nonzero:
			f.append(Field.random(randbelow))
		else:
			f.append(Field.random_nonzero(randbelow))
		
		return cls(nArray(f, [None], [Field]))
	
	@classmethod
	def random_factor(cls, Array, Field, randbelow):
		return cls.factor(Field.random(randbelow), Array)
	
	@classmethod
	def random_factor_nonzero(cls, Array, Field, randbelow):
		return cls.factor(Field.random_nonzero(randbelow), Array)
	
	def __init__(self, coefficients):
		"f[0] * x + f[1] * x**p + f[2] * x**(p * 2) + ... + f[k] * x**(p * k)"
		
		try:
			self.__f = coefficients.__f
			return
		except (AttributeError, TypeError):
			pass
		
		self.__f = coefficients
		
		if not len(self.__f) == self.Field.field_power:
			raise ValueError(f"Linear function over {self.Field.__name__} needs {self.Field.field_power} parameters.")
	
	def serialize(self):
		try:
			return self.__f.serialize()
		except AttributeError:
			return map(int, self.__f)
	
	def linear_coefficient(self, i):
		return self.__f[i]
	
	@cached
	def __str__(self):
		return " + ".join(f"{self.__f[_n]}·x{superscript(self.Field.field_base ** _n)}" for _n in range(self.Field.field_power))
	
	def __call__(self, x):
		return sum((self.__f[_n] * x**(self.Field.field_base ** _n) for _n in range(self.Field.field_power)), self.Field(0))
	
	def __add__(self, other):
		try:
			return self.__class__(self.Array((_a + _b for (_a, _b) in zip(self.__f, other.__f)), [None], [self.Field]))
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__(self.Array((_a - _b for (_a, _b) in zip(self.__f, other.__f)), [None], [self.Field]))
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		return self.__class__(self.Array((_a * other for _a in self.__f), [None], [self.Field]))
	
	def __rmul__(self, other):
		return self.__class__(self.Array((other * _a for _a in self.__f), [None], [self.Field]))
	
	def __matmul__(self, other):
		try:
			f = [self.Field(0)] * self.Field.field_power
			
			for m in range(self.Field.field_power):
				for n in range(other.Field.field_power):
					f[(m + n) % self.Field.field_power] += self.__f[m] * other.__f[n]**(self.Field.field_base ** m)
			
			return self.__class__(self.Array(f, [None], [self.Field]))
		
		except AttributeError:
			return NotImplemented


class Quadratic:
	"Class of functions of 2 variables, containing the product `f(x, y) = x * y` and closed over linear transformations."
	
	@property
	def Field(self):
		return self.__f[0].Field
	
	@property
	def Linear(self):
		return self.__f[0].Linear
	
	@classmethod
	@property
	def Quadratic(cls):
		return cls
	
	@property
	def Array(self):
		return array_fallback(self.__f.__class__)
	
	@property
	def Dictionary(self):
		try:
			return self.__f.Dictionary
		except AttributeError:
			return lambda values, Type, size, *indices: self.__f.__class__(values)
	
	@classmethod
	def zero(cls, Array, Linear, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Linear.zero(Array, Field) for _i in range(Field.field_power)), [Field.field_power, None], [Linear, Field]))
	
	@classmethod
	def one(cls, Array, Linear, Field):
		nArray = array_fallback(Array)
		return cls(nArray((chain([Linear.one(Array, Field)], (Linear.zero(Array, Field) for _i in range(Field.field_power)))), [Field.field_power, None], [Linear, Field]))
	
	@classmethod
	def random(cls, Array, Linear, Field, randbelow):
		nArray = array_fallback(Array)
		return cls(nArray((Linear.random(Array, Field, randbelow) for _i in range(Field.field_power)), [Field.field_power, None], [Linear, Field]))
	
	def __init__(self, coefficients):
		"f[0](x * y) + f[1](x * y**p) + f[2](x * y ** (p ** 2)) + f[3](x * y ** (p ** 3)) + ... + f[k](x * y ** (p ** k))"
		
		try:
			self.__f = coefficients.__f
			return
		except AttributeError:
			pass
		
		self.__f = coefficients
		
		if not len(self.__f) == self.Field.field_power:
			raise ValueError(f"Linear function over {self.Field.__name__} needs {self.Field.field_power} parameters.")
	
	def serialize(self):
		try:
			return self.__f.serialize()
		except AttributeError:
			return chain.from_iterable(_v.serialize() for _v in self.__f)
	
	def quadratic_coefficient(self, i, j):
		return self.__f[i].linear_coefficient(j)
	
	def __call__(self, x, y):
		return sum((self.__f[_k](x * y**(self.Field.field_base ** _k)) for _k in range(self.Field.field_power)), self.Field(0))
	
	def __add__(self, other):
		try:
			return self.__class__(self.Array((_a + _b for (_a, _b) in zip(self.__f, other.__f)), [self.Field.field_power, None], [self.Linear, self.Field]))
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__(self.Array((_a - _b for (_a, _b) in zip(self.__f, other.__f)), [self.Field.field_power, None], [self.Linear, self.Field]))
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		return self.__class__(self.Array((_a * other for _a in self.__f), [self.Field.field_power, None], [self.Linear, self.Field]))
	
	def __rmul__(self, other):
		return self.__class__(self.Array((other * _a for _a in self.__f), [self.Field.field_power, None], [self.Linear, self.Field]))
	
	def __matmul__(self, other):
		try:
			b, c = other
		except ValueError:
			return NotImplemented
		
		m = self.Field.field_power
		p = self.Field.field_base
		
		d = defaultdict(lambda: self.Field(0))
		for (i, j, k, l) in product(range(m), repeat=4):
			d[(i + l) % m, (j + k - i) % m] += self.quadratic_coefficient(k, l) * b.linear_coefficient(i)**(p**l) * c.linear_coefficient(j)**(p ** ((k + l) % m))
		
		f = []
		for j in range(m):
			f.append(b.__class__(b.Array((d[i, j] for i in range(m)), [None], [self.Field])))
		return self.__class__(self.Array(f, [self.Field.field_power, None], [self.Linear, self.Field]))
	
	def __rmatmul__(self, other):
		return self.__class__(self.Array((other @ _f for _f in self.__f), [self.Field.field_power, None], [self.Linear, self.Field]))


class Vector:
	@property
	def Field(self):
		return self[0].Field
	
	#@property
	#def Linear(self):
	#	return self[0].Field
	
	@property
	def Array(self):
		return array_fallback(self.__values.__class__)
	
	def zero_element(self):
		#try:
		#	return self.Linear.zero()
		#except AttributeError:
		return self.Field(0)
	
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
		return cls(nArray((Field(0) for _n in range(length)), [None], [Field]))
	
	def __init__(self, values):
		if len(values) == 1:
			try:
				self.__values = values[0].__values
			except AttributeError:
				pass
			else:
				return
		
		self.__values = values
	
	def serialize(self):
		try:
			return self.__values.serialize()
		except AttributeError:
			return map(int, self.__values)
	
	@cached
	def __repr__(self):
		return f'{self.__class__.__name__}({{{ ", ".join(str(_n) + ": " + str(self.__values[_n]) for _n in self.keys()) }}})'
	
	@cached
	def __str__(self):
		return "Vector[" + ", ".join([str(_v) for _v in self.__values]) + "]"
	
	def __len__(self):
		return len(self.__values)
	
	def keys(self):
		yield from range(len(self))
	
	def values(self):
		yield from self.__values
	
	def items(self):
		yield from enumerate(self.__values)
	
	def __getitem__(self, index):
		if index is Ellipsis or (hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step')):
			return self.__class__(self.__values[index])
		else:
			return self.__values[index]
	
	#def __setitem__(self, index, value):
	#	self.__values[index] = value
	
	def __eq__(self, other):
		try:
			return len(self) == len(other) and all(self[_n] == other[_n] for _n in self.keys())
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __or__(self, other):
		return self.__class__(self.Array(chain(self, other), [None], [self.Field]))
	
	def __ror__(self, other):
		return self.__class__(self.Array(chain(other, self), [None], [self.Field]))
	
	def __add__(self, other):
		try:
			if len(self) != len(other):
				raise ValueError("Vector lengths don't match.")
			return self.__class__(self.Array((self[_n] + other[_n] for _n in self.keys()), [None], [self.Field]))
		except TypeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			if len(self) != len(other):
				raise ValueError("Vector lengths don't match.")
			return self.__class__(self.Array((self[_n] - other[_n] for _n in self.keys()), [None], [self.Field]))
		except TypeError:
			return NotImplemented
	
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
		if hasattr(other, '_Vector__values'):
			if len(self) != len(other):
				raise ValueError("Vector lengths don't match.")
			return sum((self[_n] @ other[_n] for _n in self.keys()), self.zero_element())
		elif hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__(self.Array((self[_n] @ other for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented
	
	def __rmatmul__(self, other):
		if hasattr(other, '_Vector__values'):
			if len(self) != len(other):
				raise ValueError("Vector lengths don't match.")
			return sum((other[_n] @ self[_n] for _n in self.keys()), self.zero_element())
		elif hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__(self.Array((other @ self[_n] for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented


class Matrix:
	@property
	def Field(self):
		return self[0, 0].Field
	
	@property
	def Linear(self):
		return self[0, 0].Linear
	
	def zero_element(self):
		try:
			return self.Linear.zero()
		except AttributeError:
			return self.Field(0)
	
	def __init__(self):
		self.width = 0
		self.height = 0
		self.__values = {}
		for (m, n), v in values:
			if m > self.width: self.width = m + 1
			if n > self.height: self.height = n + 1
			self.__values[m, n] = v
		
		if __debug__ and ((_m, _n) not in self.__values for (_m, _n) in self.keys()):
			raise ValueError("Matrix initializer non-contigous.")
	
	def keys(self):
		yield from product(range(self.width), range(self.height))
	
	def values(self):
		yield from self.__values.values()
	
	def items(self):
		yield from self.__values.items()
	
	def __getitem__(self, index):
		try:
			m, n = index
		except ValueError:
			raise IndexError
		return self.__values[m, n]
	
	#def __setitem__(self, index, value):
	#	try:
	#		m, n = index
	#	except ValueError:
	#		raise IndexError
	#	self.__values[index] = value
	
	def __eq__(self, other):
		try:
			return self.width == other.width and self.height == other.height and all(self[_m, _n] == other[_m, _n] for (_m, _n) in self.keys())
		except (IndexError, AttributeError):
			return NotImplemented
	
	def __add__(self, other):
		if hasattr(other, 'width') and hasattr(other, 'height'):
			if not (self.width == other.width and self.height == other.height):
				raise ValueError("Matrix dimensions don't match.")
			return self.__class__(((_m, _n), self[_m, _n] + other[_m, _n]) for (_m, _n) in self.keys())
		else:
			return NotImplemented
	
	def __sub__(self, other):
		if hasattr(other, 'width') and hasattr(other, 'height'):
			if not (self.width == other.width and self.height == other.height):
				raise ValueError("Matrix dimensions don't match.")
			return self.__class__(((_m, _n), self[_m, _n] - other[_m, _n]) for (_m, _n) in self.keys())
		else:
			return NotImplemented
	
	def __matmul__(self, other):
		if hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__(((_m, _n), self[_m, _n] @ other) for (_m, _n) in self.keys())
		elif hasattr(other, 'length'):
			if self.height != other.length:
				raise ValueError("Matrix height does not equal vector length.")
			return other.__class__((_m, sum((self[_m, _n] @ other[_n] for _n in range(self.height)), self.zero_element())) for _m in range(self.width))
		elif hasattr(other, 'width') and hasattr(other, 'height'):
			if self.height != other.width:
				raise ValueError("Left matrix height does not equal right matrix width.")
			return self.__class__(((_m, _n), sum((self[_m, _k] @ other[_k, _n] for _k in range(self.height)), self.zero_element())) for (_m, _n) in product(range(self.width), range(other.height)))
		else:
			return NotImplemented
	
	def __rmatmul__(self, other):
		if hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__(((_m, _n), other @ self[_m, _n]) for (_m, _n) in self.keys())
		elif hasattr(other, 'length'):
			if self.width != other.length:
				raise ValueError("Matrix height does not equal vector length.")
			return other.__class__((_m, sum((other[_m] @ self[_m, _n] for _m in range(self.width)), self.zero_element())) for _n in range(self.height))
		elif hasattr(other, 'width') and hasattr(other, 'height'):
			if other.height != self.width:
				raise ValueError("Right matrix height does not equal left matrix width.")
			return self.__class__(((_m, _n), sum((other[_m, _k] @ self[_k, _n] for _k in range(other.height)), self.zero_element())) for (_m, _n) in product(range(other.width), range(self.height)))
		else:
			return NotImplemented


'''
def random_series(block, delay):
	v = Matrix.random_vector(block)
	for k in range(delay):
		v[k] += Field.random_nonzero()
		while not v: v[k] += Field.random_nonzero()
		yield Matrix.random_invertible(block) @ Matrix(v[n] if m == k % block else 0 for (m, n) in product(range(block), repeat=2)) @ Matrix.random_invertible(block)


def RaRb(A):
	Q = {(m, n):A[m - n] for (m, n) in product(range(delay), range(delay)) if m <= n else Z()}
	P = {(m, n):I() for (m, n) in product(range(delay), range(delay))}
	
	for d in range(delay, 0, -1):
		U = find_upper(Q[0, 0])
		for m, n in product(range(d), repeat=2):
			Q[m, n] *= U
			P[m, n] *= U
		S = swap_rows(rank(Q[0, 0]))
	
	return P
'''


if __debug__ and __name__ == '__main__':
	from fields import Galois
	from random import randrange
	
	F = Galois('F', 3, [1, 0, 2, 1])
	
	for n in range(100):
		a = Vector.random(4, list, F, randrange)
		b = Vector.random(4, list, F, randrange)
		c = Vector.random(4, list, F, randrange)
		f = F.random(randrange)
		g = F.random(randrange)
		
		assert len(a | b) == len(a) + len(b)
		assert a + [F(1), F(2), F(3), F(4)] == a + Vector([F(1), F(2), F(3), F(4)])
		assert a + b == b + a
		assert a - b == -(b - a)
		assert f * (a + b) == f * a + f * b
		assert f * (a - b) == f * a - f * b
		assert a @ b == b @ a
		assert a @ (b + c) == a @ b + a @ c
		assert (a + b) @ c == a @ c + b @ c
		assert (a * f) @ b == f * (a @ b)
		assert (f * a) @ b == f * (a @ b)
		assert a @ (b * f) == f * (a @ b)
		assert a @ (f * b) == f * (a @ b)
		assert (f * a) @ (g * b) == (f * g) * (a @ b)
	
	for n in range(10):
		a = Linear.random(list, F, randrange)
		b = Linear.random(list, F, randrange)
		c = F.random(randrange)
		cf = Linear.factor(c, list)
		d = F.random(randrange)
		df = Linear.factor(d, list)
		cdf = Linear.factor(c * d, list)
		
		for m in range(20):
			x = F.random(randrange)
			y = F.random(randrange)
			
			assert a(x + y) == a(x) + a(y)
			assert b(x + y) == b(x) + b(y)
			assert a(x - y) == a(x) - a(y)
			assert b(x - y) == b(x) - b(y)
			assert (a + b)(x) == a(x) + b(x)
			assert (a + b)(y) == a(y) + b(y)
			assert (a - b)(x) == a(x) - b(x)
			assert (a - b)(y) == a(y) - b(y)
			assert cf(x) == c * x
			assert cf(y) == c * y
			assert df(x) == d * x
			assert df(y) == d * y
			
			assert (a @ b)(x) == a(b(x))
			assert (a @ b)(y) == a(b(y))
			assert (b @ a)(x) == b(a(x))
			assert (b @ a)(y) == b(a(y))
			
			assert (a @ cf)(x) == a(cf(x))
			assert (a @ cf)(x) == a(c * x)
			assert (cf @ a)(x) == cf(a(x))
			assert (cf @ a)(x) == c * a(x)
			
			assert cdf(x) == c * d * x
	
	for n in range(20):
		a1 = Quadratic.random(list, Linear, F, randrange)
		a2 = Quadratic.random(list, Linear, F, randrange)
		b = Linear.random(list, F, randrange)
		c = Linear.random(list, F, randrange)
		d = Linear.random(list, F, randrange)
		e = F.random(randrange)
		
		for m in range(20):
			x = F.random(randrange)
			y = F.random(randrange)
			
			assert (d @ a1 @ (b, c))(x, y) == d(a1(b(x), c(y)))
			assert (d @ a2 @ (b, c))(x, y) == d(a2(b(x), c(y)))
			assert (a1 + a2)(x, y) == a1(x, y) + a2(x, y)
			assert (a1 - a2)(x, y) == a1(x, y) - a2(x, y)
			#print(type(a1 * e))
			assert isinstance(a1 * e, Quadratic)
			assert (a1 * e)(x, y) == e * a1(x, y)
			#print(type(e * a2))
			assert isinstance(e * a2, Quadratic)
			assert (e * a2)(x, y) == e * a2(x, y)





