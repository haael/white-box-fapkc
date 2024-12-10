#!/usr/bin/python3


__all__ = 'UnivariatePolynomial', 'BivariatePolynomial'


from itertools import zip_longest, product, chain, repeat
from math import sqrt, ceil, comb as newton_binomial
from collections import defaultdict
from functools import reduce
from operator import __mul__

from utils import superscript, cached, array_fallback, table_fallback



def karatsuba(z, a, b):
	"Karatsuba's „divide and conquer” polynomial multiplication algorithm."
	
	if len(a) != len(b):
		raise ValueError("Input sequences must be of equal length.")

	if len(a) == 0:
		raise ValueError("Sequences must not be empty.")
	
	if len(a) == 1:
		return [a[0] * b[0], z]
	
	if len(a) % 2 != 0:
		raise ValueError("Sequences' length must be a power of 2.")
	
	n = len(a) // 2
	
	al = a[:n]
	ar = a[n:]
	if len(al) < len(ar):
		al.append(z)
	
	bl = b[:n]
	br = b[n:]
	if len(bl) < len(br):
		bl.append(z)
	
	aa = [_x + _y for _x, _y in zip(al, ar)]
	bb = [_x + _y for _x, _y in zip(bl, br)]
	
	ll = karatsuba(z, al, bl)
	mm = karatsuba(z, aa, bb)
	rr = karatsuba(z, ar, br)
	
	if len(ll) < len(a):
		ll.append(z)
	if len(rr) < len(a):
		rr.append(z)
	
	result = ll + rr
	for i, (l, m, r) in enumerate(zip(ll, mm, rr)):
		result[i + n] -= l - m + r
	
	assert len(result) == 2 * len(a)
	return result


class UnivariatePolynomial:
	@property
	@cached
	def Field(self):
		return self.__values[0].Field
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__values.__class__)
	
	@classmethod
	def zero(cls, Array, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Field.zero() for _n in range(Field.field_size - 1)), [None], [Field]))
	
	@classmethod
	def one(cls, Array, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Field.one() if _n == 0 else Field.zero() for _n in range(Field.field_size - 1)), [None], [Field]))
	
	@classmethod
	def ident(cls, Array, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Field.one() if _n == (0 if Field.field_size == 2 else 1) else Field.zero() for _n in range(Field.field_size - 1)), [None], [Field]))
	
	@classmethod
	def random(cls, Array, Field, randbelow):
		nArray = array_fallback(Array)
		return cls(nArray((Field.random(randbelow) for _n in range(Field.field_size - 1)), [None], [Field]))
	
	def __init__(self, values):
		try:
			self.__values = values.__values
		except AttributeError:
			self.__values = values
		
		if __debug__:
			if len(self.__values) != self.Field.field_size - 1:
				raise ValueError("Number of polynomial coefficients must be field size less one.")
	
	def serialize(self):
		try:
			return self.__values.serialize()
		except AttributeError:
			return self.__values
	
	def __getitem__(self, n):
		return self.__values[n]
	
	@cached
	def __str__(self):
		if self:
			return " + ".join(f"{str(self[_n])}·x{superscript(_n if _n else (self.Field.field_size - 1))}" for _n in range(self.Field.field_size - 1))
		else:
			return f"{self.Field.zero()}·x{superscript(self.Field.field_size - 1)}"
	
	@cached
	def __repr__(self):
		return f'{self.__class__.__name__}({repr(self.__values)})'
	
	def __bool__(self):
		return any(self.__values)
	
	def __call__(self, x):
		return self.Field.sum(self[_n] * (x ** (_n if _n else (self.Field.field_size - 1))) for _n in range(self.Field.field_size - 1))
	
	def __eq__(self, other):
		try:
			return self.Field == other.Field and all(self[_n] == other[_n] for _n in range(self.Field.field_size - 1))
		except (AttributeError, TypeError):
			return NotImplemented
	
	def __pos__(self):
		return self
	
	def __neg__(self):
		return self.__class__(self.Array((-self[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
	
	def __add__(self, other):
		try:
			if other.Field != self.Field:
				return NotImplemented
			return self.__class__(self.Array((self[_n] + other[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
		except AttributeError:
			return NotImplemented
		except TypeError:
			return self.__class__(self.Array((self[_n] + other if _n == 0 else self[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
	
	def __radd__(self, other):
		try:
			if other.Field != self.Field:
				return NotImplemented
			return self.__class__(self.Array((other[_n] + self[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
		except AttributeError:
			return NotImplemented
		except TypeError:
			return self.__class__(self.Array((other + self[_n] if _n == 0 else self[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
	
	def __sub__(self, other):
		try:
			if other.Field != self.Field:
				return NotImplemented
			return self.__class__(self.Array((self[_n] - other[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
		except AttributeError:
			return NotImplemented
		except TypeError:
			return self.__class__(self.Array((self[_n] - other if _n == 0 else self[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
	
	def __rsub__(self, other):
		try:
			if other.Field != self.Field:
				return NotImplemented
			return self.__class__(self.Array((other[_n] - self[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
		except AttributeError:
			return NotImplemented
		except TypeError:
			return self.__class__(self.Array((other - self[_n] if _n == 0 else -self[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
		
	def __mul__(self, other):
		try:
			if other.Field != self.Field:
				return NotImplemented
			
			if self.Field.field_base != 2:
				return self.__class__(self.Array((self.Field.sum(self[_n] * other[(_m - _n) % (self.Field.field_size - 1)] for _n in range(self.Field.field_size - 1)) for _m in range(self.Field.field_size - 1)), [None], [self.Field]))
			
			z = self.Field.zero()
			a = [z] + self.__values[1:] + [self.__values[0]]
			b = [z] + other.__values[1:] + [other.__values[0]]
			r = karatsuba(z, a, b)

			assert len(r) == 2 * self.Field.field_size
			assert r[0] == z
			assert r[1] == z
			assert r[2 * self.Field.field_size - 1] == z
			
			r[0] = r[-2]
			r[1] = r[-1]
			
			f = [r[_n] + r[_n + self.Field.field_size - 1] for _n in range(self.Field.field_size - 1)]
			#print(len(f), f)
			#raise NotImplementedError

			return self.__class__(self.Array(f, [None], [self.Field]))


		except (AttributeError, TypeError):
			try:
				return self.__class__(self.Array((self[_n] * other for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
			except TypeError:
				return NotImplemented
	
	def __rmul__(self, other):
		return self.__class__(self.Array((other * self[_n] for _n in range(self.Field.field_size - 1)), [None], [self.Field]))
	
	@cached
	def __pow__(self, exponent):
		if exponent < 0: # negative power
			raise ArithmeticError
		
		if exponent == 0:
			"Zero exponent. Return 1 if base is nonzero, else raise exception."
			
			if self:
				return self.one(self.Array, self.Field)
			else:
				raise ArithmeticError
		
		if exponent % (self.Field.field_size - 1) == 0:
			"Exponent divisible by field size less 1. Return 1 if base is nonzero, else 0."
			
			return self.one(self.Array, self.Field) if self else self
		
		if exponent % (self.Field.field_size - 1) == 1:
			"Exponent greater by 1 than multiplicity of field size less 1. Return base."
			return self
		
		if not self:
			"Base is 0, return 0."
			return self
		
		if 0 < exponent < self.Field.field_base:
			#"Exponent between 0 and field base (non inclusive). Calculate result through repeated multiplication."
			#return reduce(__mul__, repeat(self, exponent))
			a = exponent // 2
			b = exponent - a
			return self**a * self**b
		
		if exponent > self.Field.field_size - 1:
			"Exponent greater than field size minus 1. Crop exponent using identity: self**exponent = self**(exponent % (field_size - 1))."
			return self ** (exponent % (self.Field.field_size - 1))
		
		"Check if the exponent is divisible by a power of field base."
		n = 0
		while exponent % (self.Field.field_base ** (n + 1)) == 0:
			n += 1
		
		if n:
			"Exponent divisible by a power of field base. Use identity: self**exponent = self**(field_base ** n) * self**rest; exponent = (field_base ** n) * rest"
			f = [None] * (self.Field.field_size - 1)
			for k in range(self.Field.field_size - 1):
				f[(self.Field.field_base ** n * k) % (self.Field.field_size - 1)] = self[k] ** self.Field.field_base ** n
			a = self.__class__(self.Array(f, [None], [self.Field]))
			b = a ** (exponent // (self.Field.field_base ** n))
			return b
		else:
			"Exponent not divisible by a power of field base."
			
			"Find the greatest power of field base smaller than the exponent."
			n = 0
			while self.Field.field_base ** (n + 1) < exponent:
				n += 1
			
			a = self ** (exponent - exponent % (self.Field.field_base ** n))
			b = self ** (exponent % (self.Field.field_base ** n))
			return a * b
	
	def __matmul__(self, other): # FIXME: bug for field_base != 2 when other(x) == 0
		try:
			if other.Field != self.Field:
				return NotImplemented
			
			size_less_1 = self.Field.field_size - 1
			
			r = self.zero(self.Array, self.Field)
			for n in range(size_less_1):
				r += self[n] * (other ** (n if n else size_less_1))
			return r
		
		except AttributeError:
			return NotImplemented


class BivariatePolynomial:
	@classmethod
	def zero(cls, Array, UnivariatePolynomial, Field):
		nArray = array_fallback(Array)
		return cls(nArray((UnivariatePolynomial.zero(Array, Field) for _n in range(Field.field_size)), [Field.field_size, None], [UnivariatePolynomial, Field]))
	
	@classmethod
	def random(cls, Array, UnivariatePolynomial, Field, randbelow):
		nArray = array_fallback(Array)
		return cls(nArray((UnivariatePolynomial.random(Array, Field, randbelow) for _n in range(Field.field_size)), [Field.field_size, None], [UnivariatePolynomial, Field]))
	
	def __init__(self):
		raise NotImplementedError
	
	def __call__(self, x, y):
		_0 = self.Field.zero()
		return self.Field.sum(self[_n](x) * ((y ** _n) if y else _0) for _n in range(self.Field.field_size))
	
	def __getitem__(self, n):
		try:
			i, j = n
		except TypeError:
			return self.__values[n]
		else:
			return self.__values[i][j]
	
	@cached
	def __str__(self):
		if self:
			return " + ".join(f"{str(self[_m, _n])}·x{superscript(_m)}·y{superscript(_n)}" for (_m, _n) in product(range(self.Field.field_size), range(self.Field.field_size)))
		else:
			return f"0{subscript(self.Field.field_base)}·x⁰"


class NonUniform:
	def __init__(self, free, poly):
		raise NotImplementedError
		self.free = free
		self.poly = poly
	
	def __call__(self, *args):
		return self.poly(*args) + self.free
	
	def __add__(self, other):
		try:
			return self.__class__(self.free + other.free, self.poly + other.poly)
		except AttributeError:
			pass
		
		try:
			return self.__class__(self.free, self.poly + other)
		except TypeError:
			pass
		
		try:
			return self.__class__(self.free + other, self.poly)
		except TypeError:
			pass
		
		return NotImplemented
	
	def __radd__(self, other):
		try:
			return self.__class__(other.free + self.free, other.poly + self.poly)
		except AttributeError:
			pass
		
		try:
			return self.__class__(self.free, other + self.poly)
		except TypeError:
			pass
		
		try:
			return self.__class__(other + self.free, self.poly)
		except TypeError:
			pass
		
		return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__(self.free - other.free, self.poly - other.poly)
		except AttributeError:
			pass
		
		try:
			return self.__class__(self.free, self.poly - other)
		except TypeError:
			pass
		
		try:
			return self.__class__(self.free - other, self.poly)
		except TypeError:
			pass
		
		return NotImplemented
	
	def __rsub__(self, other):
		try:
			return self.__class__(other.free - self.free, other.poly - self.poly)
		except AttributeError:
			pass
		
		try:
			return self.__class__(-self.free, other - self.poly)
		except TypeError:
			pass
		
		try:
			return self.__class__(other - self.free, -self.poly)
		except TypeError:
			pass
		
		return NotImplemented
	
	def __mul__(self, other):
		try:
			return self.__class__(self.free * other.free, self.free * other.poly + self.poly * other.free + self.poly * other.poly)
		except AttributeError:
			pass
		
		try:
			return self.__class__(self.free.zero(), self.free * other + self.poly * other)
		except TypeError:
			pass
		
		try:
			return self.__class__(self.free * other, self.poly * other)
		except TypeError:
			pass
		
		return NotImplemented
	
	def __rmul__(self, other):
		try:
			return self.__class__(other.free * self.free, other.poly * self.free + other.free * self.poly + other.poly * self.poly)
		except AttributeError:
			pass
		
		try:
			return self.__class__(self.free.zero(), other * self.free + other * self.poly)
		except TypeError:
			pass
		
		try:
			return self.__class__(other * self.free, other * self.poly)
		except TypeError:
			pass
		
		return NotImplemented


if __debug__ and __name__ == '__main__':
	from fields import Galois
	from random import randrange
	from pycallgraph2 import PyCallGraph
	from pycallgraph2.output.graphviz import GraphvizOutput
	
	'''
	Rijndael = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	a = UnivariatePolynomial.random(list, Rijndael, randrange)
	b = UnivariatePolynomial.random(list, Rijndael, randrange)
	
	with PyCallGraph(output=GraphvizOutput(output_file=f'polynomial_multiplication.png')):
		c = a * b
	
	with PyCallGraph(output=GraphvizOutput(output_file=f'polynomial_exponentiation.png')):
		c = a ** 10
	
	quit()
	'''
	
	#fields = Galois('Binary', 2, [1, 1]), Galois('F3', 3, [1, 0, 2, 1]), Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	fields = Galois('Binary', 2, [1, 1]), Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	
	for F in fields:
		print("Polynomials over", F)
		
		_0 = F.zero()
		_1 = F.one()
		_P0 = UnivariatePolynomial.zero(list, F)
		_P1 = UnivariatePolynomial.one(list, F)
		_Pid = UnivariatePolynomial.ident(list, F)
		
		for x in F.domain():
			assert _P0(x) == _0
			assert _P1(x) == (_1 if x else _0)
			assert _Pid(x) == x
		
		for n in range(2):
			a = UnivariatePolynomial.random(list, F, randrange)
			b = UnivariatePolynomial.random(list, F, randrange)
			c = F.random(randrange)
			d = F.random(randrange)
			
			assert a(_0) == _0
			
			assert a * _0 == _P0
			assert _0 * a == _P0
			assert a * _1 == a
			assert _1 * a == a
			
			assert a + b == b + a
			assert a - b == -(b - a)
			assert a + _P0 == a
			assert _P0 + a == a
			assert a - _P0 == a
			assert _P0 - a == -a
			
			assert a * b == b * a
			assert a * _P0 == _P0
			assert _P0 * a == _P0
			assert a * _P1 == a
			assert _P1 * a == a
			
			assert a @ _P0 == _P0
			assert _P0 @ a == _P0
			assert a @ _Pid == a
			assert _Pid @ a == a
			
			if a:
				assert a ** 0 == _P1
			assert a ** 1 == a
			
			ab = a @ b
			ba = b @ a
			
			assert ab(_0) == _0
			assert ba(_0) == _0
			
			for m in range(5):
				#print("test")
				x = F.random(randrange)
				y = F.random(randrange)
				e = randrange(0, 1000)
				f = randrange(1, 20)
				
				assert (a + b)(x) == a(x) + b(x)
				assert (b + a)(y) == b(y) + a(y)
				assert (a - b)(x) == a(x) - b(x)
				assert (b - a)(y) == b(y) - a(y)
				
				assert (a * b)(x) == a(x) * b(x), f"{x}: ({a}) * ({b}) = ({a * b}) ::: {a(x)} * {b(x)} = {a(x) * b(x)} = {(a * b)(x)}"
				assert (b * a)(y) == b(y) * a(y), f"{y}: ({b}) * ({a}) = ({b * a}) ::: {b(y)} * {a(y)} = {b(y) * a(y)} = {(b * a)(y)}"
				
				assert (a * c)(x) == a(x) * c
				assert (c * a)(x) == c * a(x)
				assert (b * d)(y) == b(y) * d
				assert (d * b)(y) == d * b(y)
				
				if e:
					assert a ** e == reduce(__mul__, [a] * e), f"{a} ** {e}"
				if e and f:
					assert a ** (e + f) == a**e * a**f, f"a ** ({e} + {f}) == a**{e} * a**{f}"
					assert a ** (e * f) == (a**e)**f
				if a and e:
					assert (a ** e)(x) == a(x) ** e
				
				assert ab(x) == a(b(x)), f"{x}, {b(x)}, {a(b(x))}, {ab(x)}"
				assert ab(y) == a(b(y)), f"{y}, {b(y)}, {a(b(y))}, {ab(y)}" # FIXME: Sometimes fails for y=0. Then (a @ b)(0) should be 0 but it's not.
				assert ba(x) == b(a(x)), f"{x}, {a(x)}, {b(a(x))}, {ba(x)}"
				assert ba(y) == b(a(y)), f"{y}, {a(y)}, {b(a(y))}, {ba(y)}"



