#!/usr/bin/python3


__all__ = 'Linear', 'Quadratic', 'Vector', 'Matrix'


from itertools import zip_longest, product, chain
from math import sqrt, ceil
from collections import defaultdict

from utils import superscript, cached


class Linear:
	"Linear (uniform) function of single argument. `F(x + y) = F(x) + F(y); F(0) = 0`."
	
	@property
	def Field(self):
		return self.__f[0].Field
	
	@classmethod
	@property
	def Linear(cls):
		return cls
	
	@classmethod
	def zero(cls, Field):
		return cls(*([Field(0)] * Field.field_power))
	
	@classmethod
	def one(cls, Field):
		return cls(*([Field(1)] + [Field(0)] * (Field.field_power - 1)))
	
	@classmethod
	def factor(cls, value):
		return cls(*([value] + [value.__class__(0)] * (value.field_power - 1)))
	
	@classmethod
	def random(cls, Field, randbelow):
		return cls(*[Field.random(randbelow) for n in range(Field.field_power)])
	
	@classmethod
	def random_nonzero(cls, Field, randbelow):
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
		
		return cls(*f)
	
	@classmethod
	def random_factor(cls, Field, randbelow):
		return cls.factor(Field.random(randbelow))
	
	@classmethod
	def random_factor_nonzero(cls, Field, randbelow):
		return cls.factor(Field.random_nonzero(randbelow))
	
	def __init__(self, *args):
		"f[0] * x + f[1] * x**p + f[2] * x**(p * 2) + ... + f[k] * x**(p * k)"
		
		if len(args) == 1:
			try:
				self.__f = args[0].__f
			except AttributeError:
				pass
			else:
				return
			
			try:
				args = list(args[0])
			except TypeError:
				pass
		
		self.__f = args		
		if not len(args) == self.Field.field_power:
			raise ValueError(f"Linear function over {self.Field.__name__} needs {self.Field.field_power} parameters.")
	
	def linear_coefficient(self, i):
		return self.__f[i]
	
	@cached
	def __str__(self):
		return " + ".join(f"{self.__f[_n]}·x{superscript(self.Field.field_base ** _n)}" for _n in range(self.Field.field_power))
	
	def __call__(self, x):
		return sum((self.__f[_n] * x**(self.Field.field_base ** _n) for _n in range(self.Field.field_power)), self.Field(0))
	
	def __add__(self, other):
		try:
			return self.__class__(_a + _b for (_a, _b) in zip(self.__f, other.__f))
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__(_a - _b for (_a, _b) in zip(self.__f, other.__f))
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		return self.__class__(_a * other for _a in self.__f)
	
	def __rmul__(self, other):
		return self.__class__(other * _a for _a in self.__f)
	
	def __matmul__(self, other):
		try:
			f = [self.Field(0)] * self.Field.field_power
			
			for m in range(self.Field.field_power):
				for n in range(other.Field.field_power):
					f[(m + n) % self.Field.field_power] += self.__f[m] * other.__f[n]**(self.Field.field_base ** m)
			
			return self.__class__(*f)
		
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
	
	@classmethod
	def zero(cls, Linear, Field):
		return cls(Linear.zero(Field) for _i in range(Field.field_power))
	
	@classmethod
	def one(cls, Linear, Field):
		return cls(Linear.one(Field), *[Linear.zero(Field) for _i in range(Field.field_power)])
	
	@classmethod
	def random(cls, Linear, Field, randbelow):
		return cls(Linear.random(Field, randbelow) for _i in range(Field.field_power))
	
	def __init__(self, *args):
		"f[0](x * y) + f[1](x * y**p) + f[2](x * y ** (p ** 2)) + f[3](x * y ** (p ** 3)) + ... + f[k](x * y ** (p ** k))"
		
		if len(args) == 1:
			try:
				self.__f = args[0].__f
			except AttributeError:
				pass
			else:
				return
			
			try:
				args = list(args[0])
			except TypeError:
				pass
		
		self.__f = args
	
	def quadratic_coefficient(self, i, j):
		return self.__f[i].linear_coefficient(j)
	
	def __call__(self, x, y):
		return sum((self.__f[_k](x * y**(self.Field.field_base ** _k)) for _k in range(self.Field.field_power)), self.Field(0))
	
	def __add__(self, other):
		try:
			return self.__class__(_a + _b for (_a, _b) in zip(self.__f, other.__f))
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__(_a - _b for (_a, _b) in zip(self.__f, other.__f))
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		return self.__class__(_a * other for _a in self.__f)
	
	def __rmul__(self, other):
		return self.__class__(other * _a for _a in self.__f)
	
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
			f.append(b.__class__(d[i, j] for i in range(m)))
		return self.__class__(*f)
	
	def __rmatmul__(self, other):
		return self.__class__(other @ _f for _f in self.__f)


class Vector:
	@property
	def Field(self):
		return self[0].Field
	
	@property
	def Linear(self):
		return self[0].Field
	
	def zero_element(self):
		try:
			return self.Linear.zero()
		except AttributeError:
			return self.Field(0)
	
	@classmethod
	def random(cls, length, Field, randbelow):
		return cls((_n, Field.random(randbelow)) for _n in range(length))
	
	@classmethod
	def random_nonzero(cls, length, Field, randbelow):
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
		
		return cls(enumerate(values))
	
	@classmethod
	def zero(cls, length, Field):
		return cls((_n, Field(0)) for _n in range(length))
	
	def __init__(self, values):
		self.__values = []
		for k in values:
			try:
				n, v = k
			except TypeError:
				self.__values.append(k)
			else:
				if n >= len(self.__values):
					self.__values.extend([None] * (len(self.__values) - n + 1))
				self.__values[n] = v
		self.length = len(self.__values)
		
		if __debug__ and any(_v is None for _v in self.__values):
			raise ValueError("Vector initializer non-contigous.")
	
	@cached
	def __repr__(self):
		return f'{self.__class__.__name__}({{{ ", ".join(str(_n) + ": " + str(self.__values[_n]) for _n in self.keys()) }}})'
	
	@cached
	def __str__(self):
		return "Vector[" + ", ".join([str(_v) for _v in self.__values]) + "]"
	
	def __len__(self):
		return self.length
	
	def keys(self):
		yield from range(self.length)
	
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
			return self.length == other.length and all(self[_n] == other[_n] for _n in self.keys())
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __or__(self, other):
		return self.__class__(enumerate(chain(self, other)))
	
	def __ror__(self, other):
		return self.__class__(enumerate(chain(other, self)))
	
	def __add__(self, other):
		try:
			if len(self) != len(other):
				raise ValueError("Vector lengths don't match.")
			return self.__class__((_n, self[_n] + other[_n]) for _n in self.keys())
		except TypeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			if len(self) != len(other):
				raise ValueError("Vector lengths don't match.")
			return self.__class__((_n, self[_n] - other[_n]) for _n in self.keys())
		except TypeError:
			return NotImplemented
	
	def __neg__(self):
		return self.__class__((_n, -self[_n]) for _n in self.keys())
	
	def __mul__(self, other):
		try:
			return self.__class__((_n, self[_n] * other) for _n in self.keys())
		except TypeError:
			return NotImplemented
	
	def __rmul__(self, other):
		try:
			return self.__class__((_n, other * self[_n]) for _n in self.keys())
		except TypeError:
			return NotImplemented
	
	def __matmul__(self, other):
		if hasattr(other, 'length'):
			if self.length != other.length:
				raise ValueError("Vector lengths don't match.")
			return sum((self[_n] @ other[_n] for _n in self.keys()), self.zero_element())
		elif hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__((_n, self[_n] @ other) for _n in self.keys())
		else:
			return NotImplemented
	
	def __rmatmul__(self, other):
		if hasattr(other, 'length'):
			if self.length != other.length:
				raise ValueError("Vector lengths don't match.")
			return sum((other[_n] @ self[_n] for _n in self.keys()), self.zero_element())
		elif hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__((_n, other @ self[_n]) for _n in self.keys())
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
		a = Vector.random(4, F, randrange)
		b = Vector.random(4, F, randrange)
		c = Vector.random(4, F, randrange)
		f = F.random(randrange)
		g = F.random(randrange)
		
		assert (a | b).length == a.length + b.length
		assert a + [F(1), F(2), F(3), F(4)] == a + Vector(((0, F(1)), (1, F(2)), (2, F(3)), (3, F(4))))
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
	
	quit()
	
	for n in range(10):
		a = LinearFunction.random(F, randrange)
		b = LinearFunction.random(F, randrange)
		c = F.random(randrange)
		cf = LinearFunction.factor(c)
		d = F.random(randrange)
		df = LinearFunction.factor(d)
		cdf = LinearFunction.factor(c * d)
		
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
		a1 = QuadraticFunction.random(F, randrange)
		a2 = QuadraticFunction.random(F, randrange)
		b = LinearFunction.random(F, randrange)
		c = LinearFunction.random(F, randrange)
		d = LinearFunction.random(F, randrange)
		e = F.random(randrange)
		
		for m in range(20):
			x = F.random(randrange)
			y = F.random(randrange)
			
			assert (d @ a1 @ (b, c))(x, y) == d(a1(b(x), c(y)))
			assert (d @ a2 @ (b, c))(x, y) == d(a2(b(x), c(y)))
			assert (a1 + a2)(x, y) == a1(x, y) + a2(x, y)
			assert (a1 - a2)(x, y) == a1(x, y) - a2(x, y)
			#print(type(a1 * e))
			assert isinstance(a1 * e, QuadraticFunction)
			assert (a1 * e)(x, y) == e * a1(x, y)
			#print(type(e * a2))
			assert isinstance(e * a2, QuadraticFunction)
			assert (e * a2)(x, y) == e * a2(x, y)





