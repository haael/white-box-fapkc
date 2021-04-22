#!/usr/bin/python3
#-*- coding:utf8 -*-

"Polynomials of rings or fields."

from enum import Enum
from itertools import chain, product
from collections import defaultdict, Counter, deque
from functools import reduce
import operator
from math import log10, ceil
from weakref import WeakValueDictionary
from random import choice

from utils import Immutable, random_sample, parallel_map, parallel_starmap, canonical, optimized, evaluate, substitute
from algebra import Algebra, AlgebraicStructure
from rings import BooleanRing
from term import Term, Identical


__all__ = 'Polynomial',



class Polynomial(Immutable, AlgebraicStructure, Term):
	"Polynomials over rings and fields."
	
	symbol = Enum('Polynomial.symbol', 'var const add sub neg mul')
	
	default_ring = BooleanRing.get_algebra()
	
	algebra_kwparams_names = 'base_ring',
	
	def __init__(self, operator, operands=None, base_ring=None):
		"""
		Usage 1: `Polynomial(polynomial)` - copy the polynomial.
		Usage 2: `Polynomial(value, base_ring=Ring)` - create a constant from the base ring with the specified value (as interpreted by the constructor of the base ring).
		Usage 3: `Polynomial(operator, operands)` - raw initialization; do not use, try the convenience methods instead.
		"""
		
		assert base_ring.algebra_name != 'Polynomial' if base_ring != None else True
		
		if operands == None:
			try:
				self.p_operator = operator.p_operator
				self.p_operands = operator.p_operands
			except AttributeError:
				c = self.__class__.const(base_ring(operator))
				self.p_operator = c.p_operator
				self.p_operands = c.p_operands
		else:
			if operator not in (self.symbol.var, self.symbol.const, self.symbol.add, self.symbol.sub, self.symbol.neg, self.symbol.mul):
				raise ValueError(f"Wrong operator: {repr(operator)}")
			self.p_operator = operator
			self.p_operands = operands

		self.immutable = True
		
		assert self.algebra.algebra_name == 'Polynomial'
		assert base_ring == None or self.algebra.base_ring == base_ring
		
		# This is a very expensive check.
		assert self.is_valid_polynomial(), repr(self)
	
	def __repr__(self):
		if self.is_const():
			return self.__class__.__qualname__ + '(' + self.p_operator.name + ', [' + repr(self.const_value()) + '])'
		elif self.is_var():
			return self.__class__.__qualname__ + '(' + self.p_operator.name + ', [' + repr(self.var_name()) + '])'
		else:
			return self.__class__.__qualname__ + '(' + self.p_operator.name + ', [' + (', '.join(repr(_subterm) for _subterm in self.subterms())) + '])'
	
	def is_var(self):
		return self.p_operator == self.symbol.var
	
	def is_const(self):
		return self.p_operator == self.symbol.const
	
	def is_add(self):
		return self.p_operator == self.symbol.add
	
	def is_mul(self):
		return self.p_operator == self.symbol.mul
	
	def is_sub(self):
		return self.p_operator == self.symbol.sub
	
	def is_neg(self):
		return self.p_operator == self.symbol.neg
	
	def subterms(self):
		"Return the subterms to iterate over."
		if not self.is_const() and not self.is_var():
			return self.p_operands
		else:
			raise ValueError("Variable or constant polynomial doesn't have substructure: " + repr(self))
	
	def const_value(self):
		"Return the value of the constant (type: `self.base_ring`)."
		if self.is_const():
			return self.p_operands
		else:
			raise ValueError("Const value requested from a polynomial that is not a const.")
	
	def var_name(self):
		"Return the name of the variable (type: `str`)."
		if self.is_var():
			return self.p_operands[0]
		else:
			raise ValueError
	
	@property
	def algebra(self):
		if self.is_var():
			base_ring = self.p_operands[1]
			return self.get_algebra(base_ring=base_ring)
		elif self.is_const():
			base_ring = self.const_value().algebra
			return self.get_algebra(base_ring=base_ring)
		
		for op in self.subterms():
			if op.is_var() or op.is_const():
				return op.algebra
		
		return self.subterms()[0].algebra
	
	@property
	def base_ring(self):
		return self.algebra.base_ring
	
	@classmethod
	def var(cls, name, base_ring):
		return cls(cls.symbol.var, [name, base_ring], base_ring=base_ring)
	
	@classmethod
	def const(cls, value, base_ring=None):
		try:
			if value.algebra.algebra_name == 'Polynomial':
				raise ValueError("Polynomial can not be a constant")
		except AttributeError:
			pass
		
		if base_ring != None and (not hasattr(value, 'algebra') or value.algebra != base_ring):
			value = base_ring(value)
		
		return cls(cls.symbol.const, value, base_ring=base_ring)
	
	@classmethod
	def zero(cls, base_ring=default_ring):
		return cls.const(base_ring.zero())
	
	@classmethod
	def one(cls, base_ring=default_ring):
		return cls.const(base_ring.one())
	
	@classmethod
	def sum(cls, addends, base_ring=default_ring):
		if not isinstance(addends, list):
			addends = list(addends)
		
		if len(addends) == 0:
			return cls.zero(base_ring=base_ring)
		else:
			return cls(cls.symbol.add, addends, base_ring=base_ring)
	
	@classmethod
	def product(cls, factors, base_ring=default_ring):
		if not isinstance(factors, list):
			factors = list(factors)
		
		if len(factors) == 0:
			return cls.one(base_ring=base_ring)
		else:
			return cls(cls.symbol.mul, factors, base_ring=base_ring)
	
	@classmethod
	def random(cls, variables=None, order=0, base_ring=default_ring):
		algebra = cls.get_algebra(base_ring=base_ring)
		
		if variables == None:
			variables = []
		
		ds = []
		for n in range(order + 1):
			for m in range(min(n, order - n) + 1): # TODO: factorial
				vs = list(random_sample(iter(variables), len(variables), n)) # FIXME: sometimes fails with `empty range for randrange()`
				vs.append(algebra.const(base_ring.random()))
				monomial = algebra(cls.symbol.mul, vs)
				ds.append(monomial)
		
		return algebra(cls.symbol.add, ds)
	
	@classmethod
	def random_nonzero(cls, variables=None, order=0, base_ring=default_ring):
		algebra = cls.get_algebra(base_ring=base_ring)
		
		if variables == None:
			variables = []
		
		ds = []
		for n in range(order + 1):
			for m in range(min(n, order - n) + 1): # TODO: factorial
				vs = list(random_sample(iter(variables), len(variables), n))
				vs.append(algebra.const(base_ring.random()))
				monomial = algebra(cls.symbol.mul, vs)
				ds.append(monomial)
		
		result = algebra(cls.symbol.add, ds)
		if not result: result += base_ring.random_nonzero()
		
		return result
	
	def is_valid_polynomial(self):
		algebra = self.algebra
		base_ring = algebra.base_ring
		if self.is_var():
			try:
				self.subterms()
			except ValueError:
				pass
			else:
				return False
			name = self.var_name()
			ring = self.base_ring
			if ring != base_ring:
				return False
			return True
		elif self.is_const():
			value = self.const_value()
			return value.algebra == self.algebra.base_ring
		elif self.is_add() or self.is_mul():
			return all(operand.is_valid_polynomial() and operand.algebra == algebra for operand in self.subterms())
		elif self.is_neg():
			if len(self.subterms()) != 1:
				return False
			return all(operand.is_valid_polynomial() and operand.algebra == algebra for operand in self.subterms())
		elif self.is_sub():
			if len(self.subterms()) != 2:
				return False
			return all(operand.is_valid_polynomial() and operand.algebra == algebra for operand in self.subterms())
		else:
			return False
	
	def __add__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		return self.algebra(self.symbol.add, [self, other])
	
	def __radd__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		return self.algebra(self.symbol.add, [other, self])
	
	def __sub__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		return self.algebra(self.symbol.sub, [self, other])
	
	def __rsub__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		return self.algebra(self.symbol.sub, [other, self])
	
	def __neg__(self):
		return self.algebra(self.symbol.neg, [self])
	
	def __mul__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		return self.algebra(self.symbol.mul, [self, other])
	
	def __rmul__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		return self.algebra(self.symbol.mul, [other, self])
	
	def polynomial_order(self):
		current = self.canonical()
		if current.is_const():
			return 0
		elif current.is_var():
			return 1
		elif self.is_mul():
			return len(self.subterms())
		elif self.is_add():
			return self.subterms()[0].polynomial_order()
		else:
			raise RuntimeError
	
	def __divmod__(self, other):
		a = self.canonical()
		if self.algebra == other.algebra:
			b = other.canonical()
		else:
			b = self.algebra(other).canonical()
		one = self.algebra.one()
		zero = self.algebra.zero()
		
		if a.is_const():
			if b.is_const():
				return self.algebra.const(a.const_value() / b.const_value()), zero
			else:
				return zero, a
		
		elif a.is_var():
			if b.is_const():
				return (a * (one / b)).canonical(), zero
			elif b.is_var() and a == b:
				return one, zero
			else:
				return zero, a
		
		elif a.is_mul():
			fa = Counter(Identical(_f) for _f in a.subterms() if _f.is_var())
			ca = self.algebra.product(_f for _f in a.subterms() if _f.is_const()).canonical()
			
			if b.is_const():
				return ((ca / b) * self.algebra.product(_op.term**_exp for (_op, _exp) in fa.items())).canonical(), zero
			elif b.is_var() and Identical(b) in fa:
				fa[Identical(b)] -= 1
				return (ca * self.algebra.product(_op.term**_exp for (_op, _exp) in fa.items())).canonical(), zero
			elif b.is_mul():
				fb = Counter(Identical(_f) for _f in b.subterms() if _f.is_var())
				cb = self.algebra.product(_f for _f in b.subterms() if _f.is_const()).canonical()
				if all(fa[_key] >= fb[_key] for _key in fb.keys()):
					for key, val in fb.items():
						fa[key] -= val
					return ((ca / cb) * self.algebra.product(_op.term**_exp for (_op, _exp) in fa.items())).canonical(), zero
				else:
					return zero, a
			else:
				return zero, a
		
		elif a.is_add():
			if b.is_const():
				return self.algebra.sum(_op / b for _op in self.subterms()), zero
			elif b.is_var() or b.is_mul():
				f, r = list(zip(*[divmod(_op, b) for _op in self.subterms()]))
				return self.algebra.sum(f).canonical(), self.algebra.sum(r).canonical()
			else:
				d = zero
				t = a
				for la, lb in product(a.subterms(), b.subterms()):
					f, r = divmod(la, lb)
					if not r.is_zero(): continue
					assert la == f * lb, f"{la} == ({f}) * ({lb})"
					
					ra = (a - f * b).canonical()
					if ra.polynomial_order() >= a.polynomial_order(): continue
					g, s = divmod(ra, b)
					assert a == (f + g) * b + s
					
					if s.polynomial_order() < t.polynomial_order():
						d = f + g
						t = s
				
				return d.canonical(), t.canonical()
					
		
		raise RuntimeError
	
	def __rdivmod__(self, other):
		return divmod(self.const(other), self)
	
	def __truediv__(self, other):
		"Divide 2 polynomials. If they are not divisible, raise an error."
		quotient, remainder = divmod(self, other)
		if remainder:
			raise ArithmeticError("Remainder nonzero when dividing polynomials.")
		return quotient
	
	def __rtruediv__(self, other):
		"Divide 2 polynomials. If they are not divisible, raise an error. (Reverse method.)"
		quotient, remainder = divmod(self.algebra.const(other), self)
		if remainder:
			raise ArithmeticError("Remainder nonzero when dividing polynomials.")
		return quotient
	
	def __floordiv__(self, other):
		"Divide 2 polynomials. If they are not divisible, round down."
		try:
			if not other.algebra == self.algebra:
				other = self.algebra(other)
		except AttributeError:
			other = self.algebra(other)
		quotient, remainder = divmod(self, other)
		return quotient
	
	def __rfloordiv__(self, other):
		"Divide 2 polynomials. If they are not divisible, round down. (Reverse method.)"
		quotient, remainder = divmod(other, self)
		return quotient
	
	def __mod__(self, other):
		"Remainder of division of 2 polynomials."
		quotient, remainder = divmod(self, other)
		return remainder
	
	def __or__(self, other):
		"Return 'disjunction' of polynomials, defined as `x + y - x * y`."
		return self + other - self * other
	
	def __ror__(self, other):
		"Return 'disjunction' of polynomials, defined as `x + y - x * y`. (Reverse method.)"
		return other + self - other * self
	
	def __pow__(self, exponent):
		if exponent != 0 and (self.algebra.base_ring.size == 2 or self.is_zero() or self.is_one()):
			return self
		elif exponent == 0 and self.is_zero():
			raise ZeroDivisionError("Zero to the power of zero.")
		elif exponent < 0 and self.is_zero():
			raise ZeroDivisionError("Zero to negative power.")
		elif exponent == 0:
			return self.algebra.one()
		elif exponent == 1:
			return self
		
		assert exponent != 0
		
		if exponent >= 0:
			base = self
		else:
			base = self.algebra.one() / self
		
		result = base
		for i in range(abs(exponent) - 1):
			result *= base
			result = result.flatten()
		return result
	
	@classmethod
	def domain(cls, base_ring=default_ring):
		algebra = cls.get_algebra(base_ring=base_ring)
		for value in base_ring.domain():
			yield algebra(value)
	
	def is_jit(self):
		return self.is_const() and self.const_value().is_jit()
	
	@property
	def ring_value(self):
		c = self.evaluate()
		assert c.algebra.algebra_name != 'Polynomial'
		assert c.algebra == self.algebra.base_ring
		return c.ring_value
	
	def __int__(self):
		return int(self.evaluate())
	
	def compile(self, name, compiler):
		sorted_vars = sorted([str(_var) for _var in self.variables()])
		try:
			bl = self.algebra.exponent
		except AttributeError:
			bl = (self.algebra.base_ring.size - 1).bit_length()
		bits = (8 * ((bl - 1) // 8 + 1)) if bl > 1 else 8
		
		@compiler.function(name=name, bits=bits, arg_count=len(sorted_vars))
		def evaluate_polynomial(*args):
			result = self(**dict(zip(sorted_vars, [self.algebra.const(_arg) for _arg in args]))).evaluate()
			try:
				return result.ring_value
			except AttributeError:
				return result.binary_field_value
	
	def wrap_compiled(self, name, code):
		compiled = code.symbol[name]
		sorted_vars = sorted([str(_var) for _var in self.variables()])
		ring = self.algebra.base_ring
		def wrapped(**kwargs):
			return ring(compiled(*[int(kwargs[_v]) for _v in sorted_vars]))
		wrapped.__name__ = name
		return wrapped
	
	__hash__ = Term.__hash__
	
	def __bool__(self):
		return not self.is_zero()
	
	def __gt__(self, other):
		return self.sort_ordering() > other.sort_ordering()


if __debug__:
	import pickle
	from rings import *
	
	def test_polynomial(Polynomial):
		"Test suite for polynomials."
		
		Ring = Polynomial.base_ring
		
		yes = Ring.one()
		no = Ring.zero()
		
		assert Polynomial.const(Ring.one()) == Ring.one()
		assert Ring.one() == Polynomial.const(Ring.one())
		assert Polynomial.const(Ring.zero()) == Ring.zero()
		assert Ring.zero() == Polynomial.const(Ring.zero())
		assert Ring.one() == Polynomial.one()
		assert Ring.zero() == Polynomial.zero()
		
		assert yes != no
		assert yes == yes
		assert no == no
		
		x = Polynomial.var('x')
		y = Polynomial.var('y')
		z = Polynomial.var('z')
		
		assert Polynomial.random().algebra == Polynomial
		for v in Polynomial.domain():
			assert v.algebra == Polynomial
		
		assert pickle.loads(pickle.dumps(x)) == x
		assert pickle.loads(pickle.dumps(x)).algebra == x.algebra
		assert pickle.loads(pickle.dumps(x + y)) == x + y
		
		p_a = x * y
		p_b = pickle.dumps(x * y)
		p_c = pickle.loads(p_b)
		assert p_a == p_c
		
		assert pickle.loads(pickle.dumps(x * y)) == x * y
		
		assert x
		assert x + y
		assert not x - x
		assert x - y
		
		assert x == x
		assert y == y
		assert z == z

		assert x != y
		assert x != z
		assert y != x
		assert y != z
		assert z != x
		assert z != y
		
		assert (x + y) * (x - y) == x**2 - y**2
		assert (x + y) * (x + y) == x**2 + x * y + x * y + y**2
		assert (x + y) * (x + y) * (x + y) == x**3 + x**2 * y + x**2 * y + x**2 * y + x * y**2 + x * y**2 + x * y**2 + y**3, f"{((x + y) * (x + y) * (x + y)).canonical()} == {(x**3 + x**2 * y + x**2 * y + x**2 * y + x * y**2 + x * y**2 + x * y**2 + y**3).canonical()}"
		
		assert x // x == yes
		assert x // y == no
		assert y // x == no
		assert y // y == yes
		
		assert (x * x) // (y) == no
		assert (x * x) // (x * x) == yes
		assert (x * y) // (y * x) == yes
		
		#assert (x * x + y) // (x * x) == yes, str((x * x + y) // (x * x))
		#assert (x * x + y) // (y + x * x) == yes
		
		assert (x * y)(x=yes, y=no) == no
		assert (x * y)(x=yes, y=yes) == yes
		assert (x + y)(x=yes, y=no) == yes
		assert (x * y + x)(x=z) == (z * y + z)
		assert (x * y + x)(x=y) == no if x**2 + x == no else True
		assert (x * y)(x=z, y=z) == z if x**2 == x else True

		#print(x.canonical(), "         ", (-x).canonical(), "       ", [str(_f) for _f in ((x * x + y) * (x * x + y)).monomials()])

		
		'''
		def r():
			return Ring.random()
		
		def rn():
			return Ring.random_nonzero()
		
		field_samples_0 = frozenset([no, yes, r().canonical(), r().canonical(), r().canonical(), r().canonical()])
		field_samples_1 = frozenset([(rn() * x).canonical(), (rn() * y).canonical(), (rn() * z).canonical()])
		field_samples_2 = frozenset((r() * _x * _y).canonical() for (_x, _y) in product(field_samples_1, field_samples_1))
		field_samples_3 = frozenset((r() * _x * _y * _z).canonical() for (_x, _y, _z) in product(field_samples_1, field_samples_1, field_samples_1))
		
		field_samples_0_1 = frozenset((r() * _x + r() * _y).canonical() for (_x, _y) in product(field_samples_0, field_samples_1))
		field_samples_0_2 = frozenset((r() * _x + r() * _y).canonical() for (_x, _y) in product(field_samples_0, field_samples_2))
		field_samples_0_3 = frozenset((r() * _x + r() * _y).canonical() for (_x, _y) in product(field_samples_0, field_samples_3))
		field_samples_1_2 = frozenset((r() * _x + r() * _y).canonical() for (_x, _y) in product(field_samples_1, field_samples_2))
		field_samples_1_3 = frozenset((r() * _x + r() * _y).canonical() for (_x, _y) in product(field_samples_1, field_samples_3))
		field_samples_2_3 = frozenset((r() * _x + r() * _y).canonical() for (_x, _y) in product(field_samples_2, field_samples_3))
		
		field_samples_0_1_2 = frozenset((r() * _x + r() * _y + r() * _z).canonical() for (_x, _y, _z) in product(field_samples_0, field_samples_1, field_samples_2))
		field_samples_0_1_3 = frozenset((r() * _x + r() * _y + r() * _z).canonical() for (_x, _y, _z) in product(field_samples_0, field_samples_1, field_samples_3))
		field_samples_0_2_3 = frozenset((r() * _x + r() * _y + r() * _z).canonical() for (_x, _y, _z) in product(field_samples_0, field_samples_2, field_samples_3))
		field_samples_1_2_3 = frozenset((r() * _x + r() * _y + r() * _z).canonical() for (_x, _y, _z) in product(field_samples_1, field_samples_2, field_samples_3))
		
		field_samples_0_1_2_3 = frozenset((r() * _x + r() * _y + r() * _z + r() * _t).canonical() for (_x, _y, _z, _t) in product(field_samples_0, field_samples_1, field_samples_2, field_samples_3))
		
		field_samples = field_samples_0 | field_samples_1 | field_samples_2 | field_samples_3 | field_samples_0_1 | field_samples_0_2 | field_samples_0_3 | field_samples_1_2 | field_samples_1_3 | field_samples_2_3 | field_samples_0_1_2 | field_samples_0_1_3 | field_samples_0_2_3 | field_samples_1_2_3 | field_samples_0_1_2_3
		
		del field_samples_0, field_samples_1, field_samples_2, field_samples_3, field_samples_0_1, field_samples_0_2, field_samples_0_3, field_samples_1_2, field_samples_1_3, field_samples_2_3, field_samples_0_1_2, field_samples_0_1_3, field_samples_0_2_3, field_samples_1_2_3, field_samples_0_1_2_3
		
		test_size = min(len(field_samples), 4)
		
		for n, a in enumerate(random_sample(iter(field_samples), len(field_samples), test_size)):
			pass
		
		'''
		
		def random_polynomials(n):
			for i in range(n):
				yield Polynomial.random(variables=[x, y, z], order=3)
		
		for a in random_polynomials(32):
			
			a_canonical = a.canonical()
			for n in range(64):
				rx = Ring.random()
				ry = Ring.random()
				rz = Ring.random()
				assert a_canonical(x=rx, y=ry, z=rz) == a(x=rx, y=ry, z=rz)
			
			assert a - a == no
			assert -a == (-yes) * a
			assert yes * a == a * yes == a
			assert no * a == a * no == no
			assert yes | a == a | yes == yes
			assert no | a == a | no == a
			assert a // yes == a, f"{str(a)} : ({str(a.canonical())}) / 1 == {str(a // yes)}"
			assert a % yes == no
			assert --a == a
			assert a**1 == a
			
			try:
				assert a**0 == yes, str(a.canonical())
			except ZeroDivisionError:
				assert not a
			except ArithmeticError:
				assert yes % a
			
			# FIXME: fails
			try:
				assert (a**-1 == yes // a) or (yes % a)
			except ZeroDivisionError:
				assert not a, str(a)
			except ArithmeticError:
				assert yes % a
			
			# FIXME: fails
			try:
				assert (a * a**-1 == yes) or (yes % a)
			except ZeroDivisionError:
				assert not a
			except ArithmeticError:
				assert yes % a
			
			if Polynomial.base_ring.size == 2:
				assert a * a == a, "a = {}".format(a)
				assert -a == a
				assert a + a == no
				assert a * a + a == no
				assert a | a == a
				assert a**2 == a
		
		for a, b in product(random_polynomials(8), random_polynomials(8)):
			assert a + b == b + a
			assert a * b == b * a
			assert a - b == a + (-b) == -b + a
			assert (-a) * b == a * (-b) == -(a * b)
			assert (-a) * (-b) == a * b, f"{a.canonical()}, {b.canonical()} : {((-a) * (-b)).canonical()} == {(a * b).canonical()}"
			
			try:
				q, r = divmod(a, b)
				assert q * b + r == a, f"({str(a.canonical())}) / ({str(b.canonical())})"
				
				assert q == a // b
				assert r == a % b
			except ZeroDivisionError:
				assert not b
			except ArithmeticError:
				assert any(Ring.size % m == 0 for m in range(2, Ring.size)) # not prime
		
		for a, b, c in product(random_polynomials(4), random_polynomials(4), random_polynomials(4)):
			assert (a + b) + c == a + (b + c)
			assert (a + b) * c == a * c + b * c
			assert (a - b) * c == a * c - b * c
		
	def test_optimization(algebra, verbose=False):
		v = [algebra.var('v_' + str(_n)) for _n in range(64)]
		
		for i in range(10):
			p = algebra.random(variables=v, order=24).flatten()
			po = p.optimized()
			if verbose:
				print(" ", p.circuit_size(), p.circuit_depth(), '->', po.circuit_size(), po.circuit_depth(), "\t", str(100 - int(100 * po.circuit_size() / p.circuit_size())) + "%")
			assert po == p
			assert p.circuit_size() >= po.circuit_size()

	def test_compilation(polynomial, compile_tables=False):
		from pathlib import Path
		from itertools import product
		from jit_types import Compiler
		
		compiler = Compiler()
		
		if compile_tables:
			polynomial.base_ring.compile_tables('field', compiler)
			assert hasattr(polynomial.base_ring, 'jit_log_table')
			assert hasattr(polynomial.base_ring, 'jit_exp_table')
		else:
			assert not hasattr(polynomial.base_ring, 'jit_log_table')
			assert not hasattr(polynomial.base_ring, 'jit_exp_table')
		
		var_list = 'abcdefgh'
		v = list(map(polynomial.var, var_list))
		p1 = polynomial.random(variables=v, order=7)
		p1 = p1.optimized()
		p1.compile('p1', compiler)
		code = compiler.compile()
		p1c = p1.wrap_compiled('p1', code)
		with code:
			for vs in range(100):
				args = dict((_v, polynomial.base_ring.random()) for _v in var_list)
				assert p1(**args).evaluate() == p1c(**args)
	
	def polynomial_test_suite(verbose=False):
		if verbose: print("running test suite")
		
		for i in chain(range(2, 16), (2**_i for _i in range(5, 9))):
			ring = ModularRing.get_algebra(size=i)
			if verbose: print()
			if verbose: print("test Polynomial(base_ring=ModularRing(size={}))".format(i))
			ring_polynomial = Polynomial.get_algebra(base_ring=ring)
			if verbose: print(" ring test")
			test_ring(ring_polynomial)
			if verbose: print(" polynomial test")
			test_polynomial(ring_polynomial)
			if verbose: print(" optimization test")
			test_optimization(ring_polynomial, verbose)
			if verbose: print(" compilation test")
			test_compilation(ring_polynomial)
		
		ring = BooleanRing.get_algebra()
		if verbose: print()
		if verbose: print("test Polynomial(base_ring=BooleanRing())")
		ring_polynomial = Polynomial.get_algebra(base_ring=ring)
		if verbose: print(" ring test")
		test_ring(ring_polynomial)
		if verbose: print(" polynomial test")
		test_polynomial(ring_polynomial)
		if verbose: print(" optimization test")
		test_optimization(ring_polynomial, verbose)
		if verbose: print(" compilation test")
		test_compilation(ring_polynomial)
		
		for i in (2,): #(3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 18, 19, 23, 25, 32, 49, 64, 81, 121, 128, 256, 52, 1024):
			field = GaloisField.get_algebra(size=i)
			if verbose: print()
			if verbose: print("test Polynomial(base_ring=GaloisField(size={}))".format(i))
			field_polynomial = Polynomial.get_algebra(base_ring=field)
			if verbose: print(" ring test")
			test_ring(field_polynomial)
			if verbose: print(" field test")
			test_field(field_polynomial)
			if verbose: print(" polynomial test")
			test_polynomial(field_polynomial)
			if verbose: print(" optimization test")
			test_optimization(ring_polynomial, verbose)
			if verbose: print(" compilation test")
			test_compilation(ring_polynomial)
		
		for i in (1,): #(2, 3, 4, 5, 6, 7, 8, 16, 32, 64):
			field = BinaryField.get_algebra(exponent=i)
			if verbose: print()
			if verbose: print("test Polynomial(base_ring=BinaryField(exponent={}))".format(i))
			field_polynomial = Polynomial.get_algebra(base_ring=field)
			if verbose: print(" ring test")
			test_ring(field_polynomial)
			if verbose: print(" field test")
			test_field(field_polynomial)
			if verbose: print(" polynomial test")
			test_polynomial(field_polynomial)
			if verbose: print(" optimization test")
			test_optimization(ring_polynomial, verbose)
			if verbose: print(" compilation test")
			test_compilation(ring_polynomial)
		
		field = RijndaelField
		if verbose: print()
		if verbose: print("test Polynomial(base_ring=RijndaelField())")
		field_polynomial = Polynomial.get_algebra(base_ring=field)
		if verbose: print(" ring test")
		test_ring(field_polynomial)
		if verbose: print(" field test")
		test_field(field_polynomial)
		if verbose: print(" polynomial test")
		test_polynomial(field_polynomial)
		if verbose: print(" optimization test")
		test_optimization(ring_polynomial, verbose)
		if verbose: print(" compilation test (long multiplication)")
		test_compilation(field_polynomial, compile_tables=False)
		if verbose: print(" compilation test (log-based multiplication)")
		test_compilation(field_polynomial, compile_tables=True)
	
	__all__ = __all__ + ('test_polynomial', 'test_optimization', 'polynomial_test_suite')


if __debug__ and __name__ == '__main__':
	polynomial_test_suite(verbose=True)
	






