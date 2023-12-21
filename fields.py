#!/usr/bin/python3


__all__ = 'Field', 'Binary', 'Polynomial', 'gcd', 'Galois'


from itertools import zip_longest, product
from math import sqrt, ceil
from collections import defaultdict
from fractions import Fraction

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
	def random(cls, randbelow):
		return cls(randbelow(cls.field_size))
	
	@classmethod
	def random_nonzero(cls, randbelow):
		return cls(randbelow(cls.field_size - 1) + 1)
	
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
	
	def serialize(self):
		yield int(self)
	
	def __str__(self):
		try:
			ss = subscript(self.modulus)
		except TypeError:
			ss = ""
		return str(self.__value) + ss
	
	def __repr__(self):
		return f'{self.__class__.__name__}({repr(self.__value)})'
	
	def __bool__(self):
		return bool(self.__value)
	
	def __int__(self):
		return int(self.__value)
	
	def __hash__(self):
		return hash((self.__value, self.field_power, self.field_base))
	
	def __eq__(self, other):
		try:
			return self.__value == other.__value
		except AttributeError:
			return NotImplemented
	
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
		
		one = self.__class__(1)
		for r in self.domain():
			if r * other == self:
				return r
		else:
			raise ArithmeticError(f"Could not divide field element {str(self)} by {str(other)}.")
	
	def __pow__(self, n):
		if n >= 0:
			if n == 0 and not self:
				raise ArithmeticError("Field zero to zero power.")
			r = self.__class__(1)
			for m in range(n):
				r *= self
			return r
		else:
			if not self:
				raise ArithmeticError("Field zero to zero negative power.")
			r = self.__class__(1)
			b = r / self
			for m in range(-n):
				r *= b
			return r


class Binary(Field):
	"Binary field (modulo 2)."
	
	modulus = 2
	
	@classmethod
	def random_nonzero(cls, randbelow):
		return cls(1)
	
	@property
	def __value(self):
		return self._Field__value
	
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
	
	def __pow__(self, n):
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
	
	def __str__(self):
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
	
	def __pow__(self, n):
		if not self:
			if n == 0:
				raise ArithmeticError("Field zero to zero power.")
			elif n < 0:
				raise ArithmeticError("Field zero to zero negative power.")
			else:
				return self
		return self.exponent[(self.logarithm[self] * n) % (self.field_size - 1)]


class BinaryGalois:
	"Fast binary Galois field. Needs `field_power` attribute determining its size and irreducible polynomial `modulus` of the right degree."
	
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
	def random(cls, randbelow):
		return cls(randbelow(cls.field_size))
	
	@classmethod
	def random_nonzero(cls, randbelow):
		return cls(randbelow(cls.field_size - 1) + 1)
	
	def __init__(self, value):
		if hasattr(value, '_BinaryGalois__value'):
			self.__value = value.__value
		else:
			self.__value = value
		assert 0 <= int(self) < self.field_size
	
	def serialize(self):
		yield int(self)
	
	def __str__(self):
		return f"#{self.__value:02x}"
	
	def __repr__(self):
		return f'{self.__class__.__name__}({repr(self.__value)})'
	
	def __bool__(self):
		return bool(self.__value)
	
	def __int__(self):
		return int(self.__value)
	
	def __hash__(self):
		return hash((self.__value, self.field_power, self.field_base))
	
	def __eq__(self, other):
		try:
			return self.__value == other.__value
		except AttributeError:
			return NotImplemented
	
	def __neg__(self):
		return self
	
	def __add__(self, other):
		try:
			return self.__class__(self.__value ^ other.__value)
		except AttributeError:
			return NotImplemented
	
	__sub__ = __add__
	
	def __mul__(self, other):
		if not self:
			return self
		if not other:
			return other
		
		field_size = self.field_size
		return self.__class__(self.exponent[(self.logarithm[int(self)] + self.logarithm[int(other)]) % (field_size - 1)])
	
	__matmul__ = __mul__
	
	def __truediv__(self, other):
		if not other:
			raise ZeroDivisionError
		if not self:
			return self
		
		field_size = self.field_size
		return self.__class__(self.exponent[(self.logarithm[int(self)] - self.logarithm[int(other)]) % (field_size - 1)])
	
	def __pow__(self, n):
		if not self:
			if n == 0:
				raise ArithmeticError("Field zero to zero power.")
			elif n < 0:
				raise ArithmeticError("Field zero to zero negative power.")
			else:
				return self
		
		field_size = self.field_size
		return self.__class__(self.exponent[(self.logarithm[int(self)] * n) % (field_size - 1)])


class Polynomial:
	"Univariate polynomial ring. Needs `Field` class attribute that may be a finite field or `Fraction`. Constructor accepts coefficients starting from the highest power."
	
	@classmethod
	def domain(cls, degree, base=None):
		if base is None:
			base = cls.Field.field_size
		
		for values in product(range(base), repeat=degree):
			yield cls(*values)
	
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
				#print(value, r, m)
				v = [m]
				while r:
					r, m = divmod(r, self.Field.field_size)
					v.append(m)
				#print(v)
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
			return self.Field(0)
	
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
		return r
	
	@cached
	def __hash__(self):
		try:
			od = self.degree + 1
		except ValueError:
			od = 0
		return hash((self.__class__.__name__, tuple(self.keys()), tuple(self.items())))
	
	def __call__(self, x):
		r = self.Field(0)
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
		
		rvalues = defaultdict(lambda:self.Field(0))
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
	
	for n in range(2, ceil(sqrt(prime))):
		if prime % n == 0:
			raise ValueError(f"Provided number {prime} is not a prime.")
	
	class Modulo(Field):
		modulus = prime
	
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
		while not len(set(Fast.exponent[:-1])) == Slow.field_size - 1:
			Fast.exponent = [0] * Slow.field_size
			Fast.logarithm = [0] * Slow.field_size
			
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
		
		assert Fast.exponent[-1] == 0
		assert Fast.exponent[0] == 1
		assert Fast.logarithm[0] == 0
	
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
		zero = x.__class__(0)
		one = x.__class__(1)
		
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
		zero = x.__class__(0)
		one = x.__class__(1)
		
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
	
	def polynomial_axioms(x, y, z):
		zero = x.__class__(0)
		one = x.__class__(1)
		
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
	
	for x, y, z in product(PolynomialRational.domain(2, 3), PolynomialRational.domain(2, 3), PolynomialRational.domain(2, 3)):
		polynomial_axioms(x, y, z)
	
	#profiler.done()
	
	#profiler = PyCallGraph(output=GraphvizOutput(output_file='modulo.png'))
	#profiler.start()
	
	for m in [2, 3, 5, 7, 11, 13, 17]:
		print(m)
		
		class Modulo(Field):
			modulus = m
		
		for x, y, z in product(Modulo.domain(), Modulo.domain(), Modulo.domain()):
			field_axioms(x, y, z)
	
	#profiler.done()
	
	#profiler = PyCallGraph(output=GraphvizOutput(output_file='polynomial_modulo.png'))
	#profiler.start()
	
	for m in [2, 3, 5]:
		print(m)
		
		class Modulo(Field):
			modulus = m
		
		class PolynomialModulo(Polynomial):
			Field = Modulo
		
		for x, y, z in product(PolynomialModulo.domain(5 // m), PolynomialModulo.domain(5 // m), PolynomialModulo.domain(5 // m)):
			polynomial_axioms(x, y, z)
	
	#profiler.done()
	
	class Modulo_7(Field):
		modulus = 7
	
	class PolynomialModulo_7(Polynomial):
		Field = Modulo_7
	
	class Galois_7_3(Field):
		modulus = PolynomialModulo_7(1, 3, 1)
	
	#for x, y, z in product(Galois_7_3.domain(), Galois_7_3.domain(), Galois_7_3.domain()):
	#	field_axioms(x, y, z)

