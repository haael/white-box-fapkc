#!/usr/bin/python3


"Implementations of some composable operations over finite fields."


__all__ = 'Linear', 'Quadratic'


from itertools import product, chain, repeat
from collections import defaultdict

from utils import superscript, cached, array_fallback, table_fallback
from vectors import Matrix


class Linear:
	"Linear function of single argument. `F(x + y) = F(x) + F(y); F(0) = 0`."
	
	@property
	@cached
	def Field(self):
		return self.__f[0].Field
	
	@classmethod
	@property
	def Linear(cls):
		return cls
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__f.__class__)
	
	def zero_element(self):
		return self.Field.zero()
	
	def one_element(self):
		return self.Field.one()
	
	@classmethod
	def zero(cls, Array, Field):
		nArray = array_fallback(Array)		
		return cls(nArray((Field.zero() for _n in range(Field.field_power)), [None], [Field]))
	
	@classmethod
	def one(cls, Array, Field):
		nArray = array_fallback(Array)		
		return cls(nArray(chain([Field.one()], (Field.zero() for _n in range(Field.field_power - 1))), [None], [Field]))
	
	ident = one
	
	@classmethod
	def factor(cls, value, Array):
		nArray = array_fallback(Array)		
		Field = value.__class__
		return cls(nArray(chain([value], (Field.zero() for _n in range(Field.field_power - 1))), [None], [Field]))
	
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
	
	def __init__(self, coefficients):
		"f[0] * x + f[1] * x**p + f[2] * x**(p ** 2) + ... + f[k] * x**(p ** k)"
		
		try:
			self.__f = coefficients.__f
		except (AttributeError, TypeError):
			self.__f = coefficients
		
		if not len(self.__f) == self.Field.field_power:
			raise ValueError(f"Linear function over {self.Field.__name__} needs {self.Field.field_power} parameters. (Got {len(self.__f)})")
		
		if any(_f.Field != self.Field for _f in self.__f):
			raise ValueError(f"All elements must belong to field {self.Field}.")
	
	def __getnewargs__(self):
		return (self.__f,)
	
	def serialize(self):
		try:
			return self.__f.serialize()
		except AttributeError:
			return map(int, self.__f)
	
	@classmethod
	def deserialize(cls, Array, Field, data):
		nArray = array_fallback(Array)		
		return cls(nArray((Field.deserialize(data) for n in range(Field.field_power)), [None], [Field]))
	
	def linear_coefficient(self, i):
		return self.__f[i]
	
	def __str__(self):
		return " + ".join(f"{self.__f[_n]}·x{superscript(self.Field.field_base ** _n)}" for _n in range(self.Field.field_power))
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + ", ".join([repr(_f) for _f in self.__f]) + ')'
	
	def __call__(self, x):
		Field = self.Field
		p = Field.field_base
		n = Field.field_power
		f = self.__f
		return Field.sum(f[_n] * x**(p ** _n) for _n in range(n))
	
	def inverse(self, Table=dict):
		"Find inverse operation to this one, i.e.: `a.inverse()(a(x)) == x`. Argument `Table` is passed to `vectors.Matrix` constructor."
		
		size = self.Field.field_power
		mat = Matrix.zero(size, size, Table, self.Array, self.Field)
		
		"Find a matrix that performs the same operation on a vector of trivial field elements as this one would on the full field elements."
		for m, n in product(range(size), range(size)):
			mat[n, m] = self.__f[(m - n) % size]**(self.Field.field_base ** n)
		w = mat.determinant()
		
		"Solve a linear equation for parameters of the inverse operation: `M @ y = x` for each base vector `x`."
		result = []
		for n in range(size):
			for m in range(size):
				mat[n, m] = self.Field.one() if m == 0 else self.Field.zero()
			
			result.append(mat.determinant() / w)
			
			for m in range(size):
				mat[n, m] = self.__f[(m - n) % size]**(self.Field.field_base ** n)
		
		"Reconstruct a linear operation from the calculated parameters."
		return self.__class__(self.Array(result, [size], [self.Field]))
	
	def __add__(self, other):
		try:
			return self.__class__(self.Array((_a + _b for (_a, _b) in zip(self.__f, other.__f)), [None], [self.Field]))
		except AttributeError as error:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__(self.Array((_a - _b for (_a, _b) in zip(self.__f, other.__f)), [None], [self.Field]))
		except AttributeError:
			return NotImplemented
	
	def __pos__(self):
		return self
	
	def __neg__(self):
		return self.__class__(self.Array((-_a for _a in self.__f), [None], [self.Field]))
	
	def __mul__(self, other):
		"Multiply the linear operation by a scalar (returns linear operation) or by other linear operation (tensor product, returns quadratic operation)."
		
		try:
			if other.Field != self.Field:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		if hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			return self.__class__(self.Array((_a * other for _a in self.__f), [None], [self.Field]))
		elif hasattr(other, '_Linear__f'):
			return Quadratic(self.Array((self.__class__(self.Array((self.__f[_j] * other.__f[(_j + _i) % self.Field.field_power] for _j in range(self.Field.field_power)), [None], [self.Field])) for _i in range(self.Field.field_power)), [self.Field.field_power, None], [self.Linear, self.Field]))
		else:
			return NotImplemented
	
	def __rmul__(self, other):
		"Right-multiply the linear operation by a scalar."
		
		try:
			if other.Field != self.Field:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		if hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			return self.__class__(self.Array((other * _a for _a in self.__f), [None], [self.Field]))
		else:
			return NotImplemented
	
	def __matmul__(self, other):
		"Compose linear operations."
		
		try:
			if other.Field != self.Field:
				return NotImplemented
			
			f = [self.Field.zero()] * self.Field.field_power
			
			for m in range(self.Field.field_power):
				for n in range(other.Field.field_power):
					f[(m + n) % self.Field.field_power] += self.__f[m] * other.__f[n]**(self.Field.field_base ** m)
			
			return self.__class__(self.Array(f, [None], [self.Field]))
		
		except AttributeError:
			return NotImplemented
	
	def pow_base(self, n):
		return self.__class__(self.Array((self.__f[(_m - n) % self.Field.field_power] ** (self.Field.field_base ** n) for _m in range(self.Field.field_power)), [None], [self.Field]))
	
	def __eq__(self, other):
		try:
			return self.__f == other.__f
		except AttributeError:
			return NotImplemented
	
	def __bool__(self):
		return any(self.__f)


class Quadratic:
	"Class of functions of 2 variables, containing the product `f(x, y) = x * y` and closed over linear transformations. Generalization of bilinear forms."
	
	@property
	@cached
	def Field(self):
		return self.__f[0].Field
	
	@property
	@cached
	def Linear(self):
		return self.__f[0].Linear
	
	@classmethod
	@property
	def Quadratic(cls):
		return cls
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__f.__class__)
	
	@classmethod
	def zero(cls, Array, Linear, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Linear.zero(Array, Field) for _i in range(Field.field_power)), [Field.field_power, None], [Linear, Field]))
	
	@classmethod
	def ident_ident(cls, Array, Linear, Field):
		nArray = array_fallback(Array)
		return cls(nArray((chain([Linear.ident(Array, Field)], (Linear.zero(Array, Field) for _i in range(Field.field_power)))), [Field.field_power, None], [Linear, Field]))
	
	@classmethod
	def random(cls, Array, Linear, Field, randbelow):
		nArray = array_fallback(Array)
		return cls(nArray((Linear.random(Array, Field, randbelow) for _i in range(Field.field_power)), [Field.field_power, None], [Linear, Field]))
	
	# TODO: ident, random_nonzero
	
	def __init__(self, coefficients):
		"f[0](x * y) + f[1](x * y**p) + f[2](x * y ** (p ** 2)) + f[3](x * y ** (p ** 3)) + ... + f[k](x * y ** (p ** k))"
		
		try:
			self.__f = coefficients.__f
			return
		except AttributeError:
			pass
		
		self.__f = coefficients
		
		if not len(self.__f) == self.Field.field_power:
			raise ValueError(f"Linear function over {self.Field.__name__} needs {self.Field.field_power} parameters. (Got {len(self.__f)}.)")
	
	def __getnewargs__(self):
		return (self.__f,)
	
	def serialize(self):
		try:
			return self.__f.serialize()
		except AttributeError:
			return chain.from_iterable(_v.serialize() for _v in self.__f)
	
	@classmethod
	def deserialize(cls, Array, Linear, Field, data):
		nArray = array_fallback(Array)
		return cls(nArray((Linear.deserialize(Array, Field, data) for _i in range(Field.field_power)), [Field.field_power, None], [Linear, Field]))
	
	def __str__(self):
		return " + ".join(f"{self.quadratic_coefficient(_i, _j)}·x{superscript(self.Field.field_base ** _i)}·y{superscript(self.Field.field_base ** ((_i + _j) % self.Field.field_power))}" for (_i, _j) in product(range(self.Field.field_power), range(self.Field.field_power)))
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + ", ".join([repr(_f) for _f in self.__f]) + ')'
	
	def quadratic_coefficient(self, i, j):
		return self.__f[i].linear_coefficient(j)
	
	def __call__(self, x, y):
		Field = self.Field
		p = Field.field_base
		n = Field.field_power
		f = self.__f
		#print("calling:", type(f[0]).__name__, f[0].__call__)
		return Field.sum(f[_k](x * y**(p ** _k)) for _k in range(n))
	
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
		"Composition of quadratic operation with 2 linear operations. `(q @ (l1, l2))(x, y) = q(l1(x), l2(y))`"
		
		try:
			b, c = other
		except ValueError:
			return NotImplemented
		
		m = self.Field.field_power
		p = self.Field.field_base
		
		d = defaultdict(lambda: self.Field.zero())
		for (i, j, k, l) in product(range(m), repeat=4):
			d[(i + l) % m, (j + k - i) % m] += self.quadratic_coefficient(k, l) * b.linear_coefficient(i)**(p**l) * c.linear_coefficient(j)**(p ** ((k + l) % m))
		
		f = []
		for j in range(m):
			f.append(b.__class__(b.Array((d[i, j] for i in range(m)), [None], [self.Field])))
		
		return self.__class__(self.Array(f, [m, None], [self.Linear, self.Field]))
	
	def __rmatmul__(self, other):
		"Composition of linear operation with quadratic operation. `(l @ q)(x, y) = l(q(x, y))`"
		
		return self.__class__(self.Array((other @ _f for _f in self.__f), [self.Field.field_power, None], [self.Linear, self.Field]))
	
	def __eq__(self, other):
		try:
			return self.__f == other.__f
		except AttributeError:
			return NotImplemented
	
	def __bool__(self):
		return any(self.__f)
	
	def __pos__(self):
		return self
	
	def __neg__(self):
		return self.__class__(self.Array((-_a for _a in self.__f), [self.Field.field_power, None], [self.Linear, self.Field]))


if __debug__ and __name__ == '__main__':
	from fields import Galois
	from random import randrange	
	
	fields = Galois('Binary', 2, [1, 1]), Galois('F3', 3, [1, 0, 2, 1]), Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	
	for F in fields:
		print("Operations over", F)
		
		_0 = F.zero()
		_1 = F.one()
		
		_L0 = Linear.zero(list, F)
		_L1 = Linear.one(list, F)
		_Lid = Linear.ident(list, F)
		
		assert _L1 == _Lid
		
		print("Linear operations test.")
		for n in range(10):
			a = Linear.random(list, F, randrange)
			b = Linear.random(list, F, randrange)
			c = F.random(randrange)
			cf = Linear.factor(c, list)
			d = F.random(randrange)
			df = Linear.factor(d, list)
			cdf = Linear.factor(c * d, list)
			
			assert a + b == b + a
			assert a - b == -(b - a)
			
			assert a + _L0 == a
			assert _L0 + a == a
			assert a - _L0 == a
			assert _L0 - a == -a
			
			assert a * _0 == _L0
			assert _0 * a == _L0
			assert a * _1 == a
			assert _1 * a == a
			assert a * (-_1) == -a
			assert (-_1) * a == -a
			
			assert _L0 @ a == _L0
			assert a @ _L0 == _L0
			assert _Lid @ a == a
			assert a @ _Lid == a
			
			for m in range(20):
				x = F.random(randrange)
				y = F.random(randrange)
				
				assert (-a)(x) == a(-x)
				assert (-b)(x) == b(-x)
				assert (-a)(x) == -(a(x))
				assert (-b)(x) == -(b(x))
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
				
				assert (a * c)(x) == c * a(x)
				assert (c * a)(x) == c * a(x)
				assert (b * c)(x) == c * b(x)
				assert (c * b)(x) == c * b(x)
				
				assert cdf(x) == c * d * x
				
				assert a(x) * b(y) == (a * b)(x, y)
				
				assert a.pow_base(n)(x) == a(x) ** F.field_base ** n, f"{n}; {a}; {a.pow_base(n)}, {x}"
				assert b.pow_base(n)(y) == b(y) ** F.field_base ** n
				
				try:
					ai = a.inverse()
				except ArithmeticError:
					pass
				else:
					assert ai(a(x)) == x
					assert a(ai(x)) == x
		
		print("Quadratic operations test.")
		for n in range(10):
			a = Quadratic.random(list, Linear, F, randrange)
			b = Quadratic.random(list, Linear, F, randrange)
			c = F.random(randrange)
			
			for m in range(20):
				x1 = F.random(randrange)
				y1 = F.random(randrange)
				x2 = F.random(randrange)
				y2 = F.random(randrange)
				
				assert (-a)(x1, x2) == -(a(x1, x2))
				assert (a + b)(x1, x2) == a(x1, x2) + b(x1, x2)
				assert (a - b)(x1, x2) == a(x1, x2) - b(x1, x2)
				
				assert (a * c)(x1, x2) == c * a(x1, x2)
				assert (c * a)(x1, x2) == c * a(x1, x2)
				assert (b * c)(x1, x2) == c * b(x1, x2)
				assert (c * b)(x1, x2) == c * b(x1, x2)
				
		print("Linear vs. quadratic operations test.")
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

