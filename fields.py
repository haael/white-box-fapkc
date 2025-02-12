#!/usr/bin/python3


"Implementation of finite field arithmetics, incl. modular fields, Galois fields, binary field optimization (xor in place of addition) and fast multiplication algorithm. Also includes polynomial class with Euclidea division algorithm."


__all__ = 'Field', 'Binary', 'Polynomial', 'gcd', 'Galois'


from itertools import zip_longest, product
from math import sqrt, ceil
from collections import defaultdict
from fractions import Fraction
from typing import Self, Iterable

from utils import *


class Field:
	"Finite field template class. Needs a class attribute `modulus` that supports modulo operation. If the modulus is a prime number, this gives modular fields. If it's an irreducible polynomial, this gives Galois fields."
	
	@classmethod
	@property
	def Field(cls):
		return cls
	
	@classmethod
	@property
	@cached
	def field_power(cls):
		try:
			return cls.modulus.degree
		except AttributeError:
			return 1
	
	@classmethod
	@property
	@cached
	def field_base(cls):
		try:
			return cls.modulus.Field.modulus
		except AttributeError:
			return cls.modulus
	
	@classmethod
	@property
	@cached
	def field_size(cls):
		return cls.field_base ** cls.field_power
	
	@classmethod
	def domain(cls):
		for values in product(range(cls.field_base), repeat=cls.field_power):
			yield cls(*values)
	
	@classmethod
	def zero(cls):
		return cls(0)
	
	@classmethod
	def one(cls):
		return cls(1)
	
	@classmethod
	def random(cls, randbelow):
		return cls(randbelow(cls.field_size))
	
	@classmethod
	def random_nonzero(cls, randbelow):
		return cls(randbelow(cls.field_size - 1) + 1)
	
	@classmethod
	def sum(cls, values:Iterable[Self]):
		return sum(values, cls.zero())
	
	def __init__(self, *values):
		if len(values) == 1:
			value = values[0]
			try:
				self.__value = value.__value
				return
			except AttributeError:
				pass
		
		self.__value = self.modulus.__class__(*values)
		
		if __debug__ and not 0 <= int(self) < self.field_size:
			raise ValueError(f"Value out of bounds: 0 <= {int(self)} < {self.field_size} (class `{self.__class__.__name__}`).")
	
	def __getnewargs__(self):
		return (self.__value,)
	
	def serialize(self) -> Iterable[int]:
		yield self.__value
	
	@classmethod
	def deserialize(cls, data):
		return cls(next(data))
	
	def __str__(self) -> str:
		try:
			ss = subscript(self.modulus)
		except TypeError:
			ss = ""
		return str(self.__value) + ss
	
	def __repr__(self) -> str:
		return f'{self.__class__.__name__}({repr(self.__value)})'
	
	def __bool__(self) -> bool:
		return bool(self.__value)
	
	def __int__(self) -> int:
		return int(self.__value)
	
	def __hash__(self) -> int:
		return hash((self.__value, self.field_power, self.field_base))
	
	def __eq__(self, other) -> bool:
		try:
			return self.__value == other.__value
		except AttributeError:
			return NotImplemented
	
	def __pos__(self):
		return self
	
	def __neg__(self):
		return self.__class__((-self.__value) % self.modulus)
	
	def __add__(self, other):
		try:
			return self.__class__((self.__value + other.__value) % self.modulus)
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__((self.__value - other.__value) % self.modulus)
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		try:
			return self.__class__((self.__value * other.__value) % self.modulus)
		except AttributeError:
			return NotImplemented
	
	__matmul__ = __mul__
	
	def __truediv__(self, other):
		if not other:
			raise ZeroDivisionError(f"Division by zero field element modulo {self.modulus}.")
		
		if not self:
			return self
		
		one = self.one()
		for r in self.domain():
			if r * other == self:
				return r
		else:
			raise ArithmeticError(f"Could not divide field element {str(self)} by {str(other)}.")
	
	def __pow__(self, n:int):
		if n >= 0:
			if n == 0 and not self:
				raise ArithmeticError("Field zero to zero power.")
			r = self.one()
			for m in range(n):
				r *= self
			return r
		else:
			if not self:
				raise ArithmeticError("Field zero to zero negative power.")
			r = self.one()
			b = r / self
			for m in range(-n):
				r *= b
			return r


class Binary(Field):
	"Binary field (modulo 2)."
	
	modulus = 2
	
	@classmethod
	def random_nonzero(cls, randbelow):
		return cls.one() # one is the only nonzero value
	
	@property
	def __value(self):
		return self._Field__value
	
	@classmethod
	def sum(cls, values:Iterable[Self]):
		r = 0
		for v in values:
			r ^= v.__value
		return cls(r)
	
	def __neg__(self):
		return self
	
	def __add__(self, other):
		try:
			return self.__class__(self.__value ^ other.__value)
		except AttributeError:
			return NotImplemented
	
	__sub__ = __add__
	
	def __mul__(self, other):
		try:
			return self.__class__(self.__value & other.__value)
		except AttributeError:
			return NotImplemented
	
	__matmul__ = __mul__
	
	def __truediv__(self, other):
		if not other:
			raise ZeroDivisionError(f"Division by zero field element modulo {self.modulus}.")
		else:
			return self
	
	def __pow__(self, n:int):
		if n == 0 and not self:
			raise ArithmeticError("Field zero to zero power.")
		elif n < 0 and not self:
			raise ArithmeticError("Field zero to negative power.")
		
		return self


class FastGalois(Field):
	"Implementation of fast multiplication and division in finite field. Logarithm and exponent tables must be calculated externally."
	
	def __mul__(self, other):
		if not hasattr(other, '_Field__value'):
			return NotImplemented
		
		if not self:
			return self
		if not other:
			return other
		
		return self.exponent[(self.logarithm[self] + self.logarithm[other]) % (self.field_size - 1)]
	
	def __str__(self) -> str:
		if self.field_power == 1:
			return "#" + super().__str__() + subscript(self.field_base)
		else:
			return "#" + ".".join(str(int(self._Field__value[n])) for n in range(self.field_power)) + subscript(self.field_base)
	
	def __truediv__(self, other):
		if not other:
			raise ZeroDivisionError
		if not self:
			return self
		return self.exponent[(self.logarithm[self] - self.logarithm[other]) % (self.field_size - 1)]
	
	def __pow__(self, n:int):
		if not self:
			if n == 0:
				raise ArithmeticError("Field zero to zero power.")
			elif n < 0:
				raise ArithmeticError("Field zero to zero negative power.")
			else:
				return self
		return self.exponent[(self.logarithm[self] * n) % (self.field_size - 1)] # assumes Python semantics of modulus od negative values


class BinaryGalois: # does not inherit from `Field` class, every method must be reimplemented
	"Fast binary Galois field. Needs `field_power` attribute determining its size and irreducible polynomial `modulus` of the right degree."
	
	@classmethod
	def sum(cls, values):
		r = 0
		for v in values:
			r ^= v.__value
		return cls(r)
	
	@classmethod
	@property
	def Field(cls):
		return cls
	
	field_base = 2
	
	@classmethod
	@property
	def field_size(cls):
		return 1 << cls.field_power
	
	@classmethod
	def domain(cls):
		for value in range(cls.field_size):
			yield cls(value)
	
	@classmethod
	def zero(cls):
		return cls(0)
	
	@classmethod
	def one(cls):
		return cls(1)
	
	@classmethod
	def random(cls, randbelow):
		return cls(randbelow(cls.field_size))
	
	@classmethod
	def random_nonzero(cls, randbelow):
		return cls(randbelow(cls.field_size - 1) + 1)
	
	def __init__(self, value:int):
		try:
			self.__value = value.__value
		except AttributeError:
			self.__value = value
		
		if isinstance(value, int):
			assert 0 <= int(self) < self.field_size
	
	def __getnewargs__(self):
		return (self.__value,)
	
	def serialize(self) -> Iterable[int]:
		yield self.__value
	
	@classmethod
	def deserialize(cls, data):
		return cls(next(data))
	
	def __str__(self) -> str:
		if not isinstance(self.__value, int):
			return f"#({self.__value})"
		else:
			return f"#{self.__value:02x}"
	
	def __repr__(self) -> str:
		try:
			return f'{self.__class__.__name__}({repr(self.__value)})'
		except AttributeError:
			return '<' + self.__class__.__name__ + ': ' + repr(self.__dict__) + '>'
	
	def __bool__(self) -> bool:
		return bool(self.__value)
	
	def __int__(self) -> int:
		return int(self.__value)
	
	def __hash__(self) -> int:
		return hash((self.__value, self.field_power, self.field_base))
	
	def __eq__(self, other) -> bool:
		try:
			return self.__value == other.__value
		except AttributeError:
			return NotImplemented
	
	def __pos__(self):
		return self
	
	def __neg__(self):
		return self
	
	def __add__(self, other):
		try:
			return self.__class__(self.__value ^ other.__value)
		except AttributeError:
			return NotImplemented
	
	__sub__ = __add__
	
	def __mul__(self, other):
		try:
			other.__value
			if self.Field != other.Field:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		if not self.__value * other.__value:
			return self.zero()
		
		return self.__class__(self.exponent[(self.logarithm[self.__value] + self.logarithm[other.__value]) % (self.field_size - 1)])
	
	__matmul__ = __mul__
	
	def __truediv__(self, other):
		try:
			other.__value
			if self.Field != other.Field:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		if not other:
			raise ZeroDivisionError("Division by zero in field.")
		if not self:
			return self
		
		return self.__class__(self.exponent[(self.logarithm[self.__value] - self.logarithm[other.__value]) % (self.field_size - 1)])
	
	def __pow__(self, n:int):
		if not self:
			if n == 0:
				raise ArithmeticError("Field zero to zero power.")
			elif n < 0:
				raise ArithmeticError("Field zero to negative power.")
			else:
				return self
		
		field_size = self.field_size
		return self.__class__(self.exponent[(self.logarithm[self.__value] * (n  % (field_size - 1))) % (field_size - 1)]) # assumes Python semantics of modulus of negative values


class Polynomial:
	"""
	Univariate polynomial ring. Needs `Field` class attribute that may be a finite field or `Fraction`. Constructor accepts coefficients starting from the highest power.
	This is an "abstract" polynomial, meaning all formal powers of the X element are unequal. It is not assumed that there exists some N so that P**N = P.
	"""
	
	@classmethod
	def domain(cls, degree, base=None):
		if base is None:
			base = cls.Field.field_size
		
		for values in product(range(base), repeat=degree):
			yield cls(*values)

	@classmethod
	def zero(cls):
		return cls()
	
	@classmethod
	def one(cls):
		return cls(cls.Field.one())
	
	@classmethod
	def ident(cls):
		return cls(cls.Field.one(), cls.Field.zero())
	
	'''
	@classmethod
	def random(cls, degree, randbelow):
		return cls(randbelow(cls.Field.field_size) for _n in range(degree))
	
	@classmethod
	def random_nonzero(cls, degree, randbelow):
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
		
		return cls(values)
	
	@classmethod
	def random_maxdegree(cls, degree, randbelow):
		values = []
		nonzero = False
		for n in range(length):
			if n == 0:
				f = Field.random_nonzero(randbelow)
			else:
				f = Field.random(randbelow)
			
			values.append(f)
		
		return cls(values)
	'''
	
	def __init__(self, *values):
		if len(values) == 1:
			value = values[0]
			
			if isinstance(value, dict):
				assert all(((0 <= _k) and _v) for (_k, _v) in value.items())
				self.__values = value
				return
			
			try:
				self.__values = values[0].__values
				return
			except AttributeError:
				pass
			
			try:
				r, m = divmod(value, self.Field.field_size)
				v = [m]
				while r:
					r, m = divmod(r, self.Field.field_size)
					v.append(m)
				self.__values = {_n:self.Field(_v) for (_n, _v) in enumerate(v) if _v}
				return
			except (AttributeError, TypeError):
				pass
		
		self.__values = {_n:self.Field(_v) for (_n, _v) in enumerate(reversed(values)) if _v}
	
	def serialize(self):
		yield int(self)
	
	def __getitem__(self, n):
		values = self.__values
		if n in values:
			return values[n]
		else:
			return self.Field.zero()
	
	def __iter__(self):
		try:
			od = self.degree
		except ValueError:
			yield self[0]
		else:
			for n in range(od + 1):
				yield self[n]
	
	def items(self):
		for key in self.keys():
			yield key, self[key]
	
	def keys(self):
		return sorted(self.__values.keys())
	
	@property
	def degree(self):
		if self.__values:
			return max(self.__values.keys())
		else:
			raise ValueError("Zero polynomial does not have a degree.")
	
	@cached
	def __str__(self):
		if self:
			return " + ".join(reversed([f"{str(_v)}·x{superscript(_n)}" for (_n, _v) in self.items()]))
		else:
			return f"0{subscript(self.Field.field_base)}·x⁰"
	
	@cached
	def __repr__(self):
		return f'{self.__class__.__name__}({", ".join(repr(_value) for _value in self)})'
	
	def __bool__(self):
		return bool(self.__values)
	
	def __int__(self):
		r = 0
		for n, v in self.items():
			r += int(v) * self.Field.field_size ** n
		return int(r)
	
	@cached
	def __hash__(self):
		try:
			od = self.degree + 1
		except ValueError:
			od = 0
		return hash((self.__class__.__name__, tuple(self.keys()), tuple(self.items())))
	
	def __call__(self, x):
		r = self.Field.zero()
		for n, v in self.items():
			if n == 0:
				r += v
			else:
				r += v * (x ** n)
		return r
	
	def __eq__(self, other):
		try:
			return self.keys() == other.keys() and all(self[_n] == other[_n] for _n in self.keys())
		except (AttributeError, TypeError):
			return NotImplemented
	
	def __pos__(self):
		return self
	
	def __neg__(self):
		return self.__class__({_n:-_value for (_n, _value) in self.items()})
	
	def __add__(self, other):
		try:
			return self.__class__({_n:(self[_n] + other[_n]) for _n in frozenset().union(self.keys(), other.keys()) if self[_n] + other[_n]})
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__({_n:(self[_n] - other[_n]) for _n in frozenset().union(self.keys(), other.keys()) if self[_n] - other[_n]})
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		if not self:
			return self
		if not other:
			return other
		
		rvalues = defaultdict(lambda: self.Field.zero())
		for m, v in self.items():
			for n, w in other.items():
				rvalues[m + n] += v * w
		
		fvalues = {}
		for n, v in rvalues.items():
			if v:
				fvalues[n] = v
		
		return self.__class__(fvalues)
	
	def __divmod__(self, other):
		if not other:
			raise ZeroDivisionError("Division by zero polynomial.")
		
		if not self:
			return self, self
		
		od = other.degree
		r = other[od]
		quotient = self.__class__()
		remainder = self
		
		while remainder and (n := remainder.degree) >= od:
			d = remainder[n]
			if not d: continue
			q = self.__class__({(n - od):(d / r)})
			remainder -= q * other
			quotient += q
		
		assert (not remainder) or (other and (remainder.degree < other.degree))
		
		return quotient, remainder
	
	def __floordiv__(self, other):
		q, r = divmod(self, other)
		return q
	
	def __mod__(self, other):
		q, r = divmod(self, other)
		return r


def gcd(p, q):
	"Calculate greatest common divisor of the provided polynomials."
	
	if not p:
		return q
	elif not q:
		return p
	elif p.degree > q.degree:
		return gcd(p % q, q)
	else:
		return gcd(p, p % q)


def Galois(name, prime, coefficients):
	"Construct Galois field with the specified `prime` base and polynomial specified in `coefficients` (starting from the highest power)."
	
	for n in range(2, ceil(sqrt(int(prime)))):
		if prime % n == 0:
			raise ValueError(f"Provided number {prime} is not a prime.")
	
	class Modulo(Field):
		modulus = prime
	
	if list(coefficients) == [1, 1]:
		Modulo.__name__ = name.split('.')[-1]
		Modulo.__qualname__ = name
		Modulo.__module__ = None
		return Modulo
	
	class PolynomialModulo(Polynomial):
		Field = Modulo
	
	polynomial = PolynomialModulo(*coefficients)
	
	class Slow(Field):
		modulus = polynomial
	
	if prime == 2:
		class Fast(BinaryGalois):
			field_power = len(coefficients) - 1
		
		Fast.exponent = [0] * Slow.field_size
		Fast.logarithm = [0] * Slow.field_size
		
		gg = 0
		while True:
			Fast.exponent = [0] * Slow.field_size
			Fast.logarithm = [0] * Slow.field_size
			Fast.logarithm[0] = Slow.field_size - 1
			
			gg += 1
			if gg >= Slow.field_size:
				raise ValueError("Generator not found in field. (Polynomial not irreducible?)")
			generator = Slow(gg)
			
			element = Slow(1)
			for n in range(Slow.field_size - 1):
				g = int(Fast(element))
				Fast.exponent[n] = g
				Fast.logarithm[g] = n
				element *= generator
			
			if len(set(Fast.exponent[:-1])) == Slow.field_size - 1:
				break
		
		assert Fast.exponent[-1] == 0
		assert Fast.exponent[0] == 1, str(Fast.exponent)
		assert Fast.logarithm[0] == (-1) % Fast.field_size, str(Fast.logarithm)
	
	else:
		class Fast(FastGalois):
			modulus = polynomial
		
		Fast.exponent = {}
		Fast.logarithm = {}
		
		gg = 0
		while not len(set(Fast.exponent.values())) == Slow.field_size - 1:
			Fast.exponent = {}
			Fast.logarithm = {}
			
			gg += 1
			if gg >= Slow.field_size:
				raise ValueError("Generator not found in field. (Polynomial not irreducible?)")
			generator = Slow(gg)
			
			element = Slow(1)
			for n in range(Slow.field_size - 1):
				g = Fast(element)
				Fast.exponent[n] = g
				Fast.logarithm[g] = n
				element *= generator
		
		assert Fast.exponent[0] == Fast(1)
	
	Fast.__name__ = name.split('.')[-1]
	Fast.__qualname__ = name
	Fast.__module__ = None
	return Fast


if __debug__:
	def ring_axioms(x, y, z):
		zero = x.zero()
		one = x.one()
		
		assert not zero
		assert one
		assert zero != one
		
		assert x + zero == x
		assert x + one != x
		assert x + y == y + x
		assert (x + y) + z == x + (y + z)
		
		assert x * zero == zero
		assert x * one == x
		assert x * y == y * x
		assert (x * y) * z == x * (y * z)
		
		assert -zero == zero
		
		assert x - x == zero
		assert x - y == x + (-y)
		
		assert x * (y + z) == x * y + x * z
	
	def field_axioms(x, y, z):
		zero = x.zero()
		one = x.one()
		
		ring_axioms(x, y, z)
		
		try:
			x / zero
		except ZeroDivisionError:
			pass
		else:
			assert False, "Division by zero should raise exception."
		
		assert one / one == one
		if x != zero and x != one: assert one / x != one
		if y: assert x / y == x * (one / y)
		if z: assert (x + y) / z == x / z + y / z
		
		if x:
			assert x ** 0 == one
			assert x ** 1 == x
			assert x ** 2 == x * x
			assert x ** 3 == x * x * x
			
			assert one / x == x ** -1
			
			assert x ** (x.field_size - 1) == one
			
			m = int(y)
			n = int(z)
			#print("**", x.field_size, m, n, m + n, (m + n) % x.field_size)
			assert (x ** m) * (x ** n) == x ** (m + n) == x ** ((m + n) % (x.field_size - 1))
			assert (x ** m) * (x ** -n) == x ** (m - n) == x ** ((m - n) % (x.field_size - 1))
			assert (x ** -m) * (x ** n) == x ** (-m + n) == x ** ((-m + n) % (x.field_size - 1))
			assert (x ** -m) * (x ** -n) == x ** (-m - n) == x ** ((-m + -n) % (x.field_size - 1))
		
		else:
			m = int(y)
			try:
				x ** m == zero
			except ArithmeticError:
				assert not m
	
	def polynomial_axioms(x, y, z):
		zero = x.zero()
		one = x.one()
		
		try:
			zero.degree
		except ValueError:
			pass
		else:
			assert False, "Zero polynomial should not have a degree."
		
		assert one.degree == 0
		
		if x:
			x.degree >= 0
		
		ring_axioms(x, y, z)
		
		if y:
			p, q = divmod(x, y)
			assert x // y == p
			assert x % y == q
			assert x == p * y + q
			
			if q:
				assert q.degree <= y.degree
		
		if x and y:
			assert gcd(x, y).degree <= x.degree
			assert gcd(x, y).degree <= y.degree	
			assert x % gcd(x, y) == zero
			assert y % gcd(x, y) == zero


if __debug__ and __name__ == '__main__':
	from random import sample
	
	#from pycallgraph2 import PyCallGraph
	#from pycallgraph2.output.graphviz import GraphvizOutput
	
	#print("running tests...")
	
	F = Galois('F', 3, [1, 0, 2, 1])
	for n in range(F.field_size):
		assert int(F(n)) == n, str(n)
	
	#profiler = PyCallGraph(output=GraphvizOutput(output_file='polynomial.png'))
	#profiler.start()
	
	class PolynomialRational(Polynomial):
		Field = Fraction
		Field.zero = lambda: Fraction(0)
		Field.one = lambda: Fraction(1)
	
	for x, y, z in product(PolynomialRational.domain(2, 3), PolynomialRational.domain(2, 3), PolynomialRational.domain(2, 3)):
		polynomial_axioms(x, y, z)
	
	#profiler.done()
	
	#profiler = PyCallGraph(output=GraphvizOutput(output_file='modulo.png'))
	#profiler.start()
	
	for m in [2, 3, 5, 7, 11, 13, 17]:
		print("modular", m)
		
		class Modulo(Field):
			modulus = m
		
		for x, y, z in product(Modulo.domain(), Modulo.domain(), Modulo.domain()):
			field_axioms(x, y, z)
	
	#profiler.done()
	
	#profiler = PyCallGraph(output=GraphvizOutput(output_file='polynomial_modulo.png'))
	#profiler.start()
	
	for m in [2, 3, 5]:
		print("polynomial", m)
		
		class Modulo(Field):
			modulus = m
		
		class PolynomialModulo(Polynomial):
			Field = Modulo
		
		for x, y, z in product(PolynomialModulo.domain(5 // m), PolynomialModulo.domain(5 // m), PolynomialModulo.domain(5 // m)):
			polynomial_axioms(x, y, z)
	
	#profiler.done()

	F3 = Galois('F3', 3, [1, 0, 2, 1])
	print("F3", F3.field_size)
	for x, y, z in product(F3.domain(), F3.domain(), F3.domain()):
		#print(x, y, z)
		field_axioms(x, y, z)
	
	class Modulo_7(Field):
		modulus = 7
	
	class PolynomialModulo_7(Polynomial):
		Field = Modulo_7
	
	class Galois_7_3(Field):
		modulus = PolynomialModulo_7(1, 3, 1)
	
	print("galois", "7[1, 3, 1]", Galois_7_3.field_size)
	
	sample_size = 7
	for x, y, z in product(sample(sorted(Galois_7_3.domain(), key=int), sample_size), sample(sorted(Galois_7_3.domain(), key=int), sample_size), sample(sorted(Galois_7_3.domain(), key=int), sample_size)):
		field_axioms(x, y, z)
	
	Rijndael = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	
	print("rijndael", Rijndael.field_size)
	
	#for x, y, z in product(Rijndael.domain(), Rijndael.domain(), Rijndael.domain()):
	sample_size = 32
	for x, y, z in product(sample(sorted(Rijndael.domain(), key=int), sample_size), sample(sorted(Rijndael.domain(), key=int), sample_size), sample(sorted(Rijndael.domain(), key=int), sample_size)):
		field_axioms(x, y, z)


