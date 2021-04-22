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
		
		'''
		if __debug__: len(operands) # raise TypeError if `operands` is not iterable
		
		if operator != self.symbol.const and operator != self.symbol.var:
			try:
				if base_ring != None:
					algebra = self.get_algebra(base_ring=base_ring)
				else:
					algebra = operands[0].algebra
				
				if algebra.algebra_name != 'Polynomial':
					raise ValueError("Constants not allowed outside of the `const` container.")
				
				if any(_op.algebra != algebra for _op in operands[1:]):
					raise ValueError(f"All operands must be from the same ring: {operands}, expected: {algebra}.")
			except IndexError:
				pass
		
		assert len(operands) == 2 if operator == self.symbol.var else True
		assert isinstance(operands[0], str) if operator == self.symbol.var else True
		assert isinstance(operands[1], Algebra) if operator == self.symbol.var else True
		
		assert all(isinstance(_op, Polynomial) for _op in operands) if (operator != self.symbol.const and operator != self.symbol.var) else True
		
		self.p_operator = operator
		assert isinstance(operands, list), str((operator, operands))
		if operator == self.symbol.const:
			self.p_const = operands[0]
		elif operator == self.symbol.var:
			self.p_var = operands[0]
			if base_ring == None:
				self.p_algebra = operands[1]
			else:
				if self.get_algebra(base_ring=base_ring) != operands[1]:
					raise ValueError(f"Wrong algebra for variable: {self.get_algebra(base_ring=base_ring)} != {operands[1]}.")
				self.p_algebra = self.get_algebra(base_ring=base_ring)
		else:
			self.p_operands = operands
		
		assert self.algebra.algebra_name == 'Polynomial'
		
		if base_ring != None and self.algebra.base_ring != base_ring:
			raise ValueError("`base_ring` = {} does not match operand algebra {}.".format(base_ring, self.algebra))
		
		self.immutable = True
		
		# This is a very expensive check.
		assert self.is_valid_polynomial(), repr(self)
		'''
	
	#def __getnewargs_ex__(self):
	#	return (self.p_operator, self.p_operands)
	
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
		return cls(cls.symbol.var, [name, base_ring])
	
	@classmethod
	def const(cls, value, base_ring=None):
		try:
			if value.algebra.algebra_name == 'Polynomial':
				raise ValueError("Polynomial can not be a constant")
		except AttributeError:
			pass
		
		if base_ring != None and value.algebra != base_ring:
			value = base_ring(value)
		return cls(cls.symbol.const, value)
	
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
	
	'''
	@staticmethod
	def __monomial_division(dividend, divisor):
		if not dividend.is_multiplicative_normal_form():
			raise ValueError("Dividend must be in multiplicative normal form.")
		if not divisor.is_canonical_monomial():
			raise ValueError("Divisor must be a monomial in canonical form.")
		
		assert dividend.algebra == divisor.algebra
		
		Ring = dividend.algebra.base_ring
		
		dividend_vars = Counter()
		dividend_factors = list()
		if dividend.operator == dividend.symbol.mul:
			if dividend.operands[0].operator == dividend.symbol.const:
				dividend_factor = dividend.operands[0].operands[0]
				for v in dividend.operands[1:]:
					if v.is_canonical_literal():
						dividend_vars[v] += 1
					else:
						dividend_factors.append(v)
			else:
				dividend_factor = Ring.one()
				for v in dividend.operands:
					if v.is_canonical_literal():
						dividend_vars[v] += 1
					else:
						dividend_factors.append(v)
		elif dividend.operator == dividend.symbol.const:
			if dividend.operands:
				dividend_factor = dividend.operands[0]
			else:
				dividend_factor = Ring.zero()
		elif dividend.operator == dividend.symbol.var:
			dividend_factor = Ring.one()
			dividend_vars[dividend] += 1
		
		divisor_vars = Counter()
		if divisor.operator == divisor.symbol.mul:
			if divisor.operands[0].operator == divisor.symbol.const:
				divisor_factor = divisor.operands[0].operands[0]
				for v in divisor.operands[1:]:
					assert v.is_canonical_literal()
					divisor_vars[v] += 1
			else:
				divisor_factor = Ring.one()
				for v in divisor.operands:
					assert v.is_canonical_literal()
					divisor_vars[v] += 1
		elif divisor.operator == divisor.symbol.const:
			if divisor.operands:
				divisor_factor = divisor.operands[0]
			else:
				divisor_factor = Ring.zero()
		elif divisor.operator == divisor.symbol.var:
			divisor_factor = Ring.one()
			divisor_vars[divisor] += 1
		
		for v in divisor_vars.keys():
			if dividend_vars[v] < divisor_vars[v]:
				raise ArithmeticError("Monomials not divisible.")
			else:
				dividend_vars[v] -= divisor_vars[v]
		
		result = dividend.const(dividend_factor / divisor_factor)
		for v in dividend_vars.elements():
			result *= v
		for v in dividend_factors:
			result *= v
		return result.flatten()
	
	@staticmethod
	def __monomial_order(monomial):
		if not monomial.is_canonical_monomial():
			raise ValueError("Argument must be in a canonical form.")
		
		if monomial.operator not in [monomial.symbol.mul, monomial.symbol.const, monomial.symbol.var]:
			raise ValueError("Argument is not a monomial.")
		
		if monomial.operator == monomial.symbol.mul:
			if monomial.operands[0].symbol == monomial.symbol.const:
				return len(monomial.operands) - 1
			else:
				return len(monomial.operands)
		elif monomial.operator == monomial.symbol.const:
			return 0
		elif monomial.operator == monomial.symbol.var:
			return 1
	
	def __divmod__(self, other):
		"Polynomial Euclidean division. For arguments `self`, `other` returns a pair `f`, `r` so that `self == other * f + r`."
		
		if self.algebra != other.algebra:
			divisor = self.algebra.const(other)
		
		Ring = self.algebra
		
		try:
			if other.is_zero():
				raise ZeroDivisionError("Division by zero in polynomial Euclidean division.")
			elif other.is_one():
				return self, Ring.zero()
		except ValueError:
			pass
		
		if self.is_multiplicative_normal_form() and other.is_canonical_monomial():
			try:
				return self.__monomial_division(self, other), Ring.zero()
			except ArithmeticError:
				pass
		
		if other.is_canonical_polynomial():
			divisor = other
		else:
			try:
				divisor = other.canonical()
			except AttributeError:
				return NotImplemented
		
		if self.is_canonical_polynomial():
			dividend = self
		else:
			dividend = self.canonical()
		
		assert dividend.algebra == divisor.algebra
		
		try:
			if dividend.is_zero():
				return Ring.zero(), Ring.zero()
		except ValueError:
			pass
		
		try:
			d = next(iter(divisor)) # leading term of the divisor
		except TypeError:
			d = self.const(divisor)
		except StopIteration:
			raise ZeroDivisionError("Division by zero in polynomial Euclidean division.")
		
		d = d.canonical()
		do = self.__monomial_order(d)
		
		result = Ring.zero()
		running = True
		while running:
			for x in dividend:
				if self.__monomial_order(x) < do:
					running = False
					break
				try:
					c = self.__monomial_division(x, d)
					assert c, "{} / {} = {}".format(x, d, c)
					result += c
					dividend -= c * divisor
					with AllowCanonical():
						dividend = dividend.canonical()
					assert dividend.is_canonical_polynomial(), dividend
					running = bool(dividend)
					break
				except ArithmeticError:
					pass
			else:
				running = False
				pass
		
		if not hasattr(result, 'operator'):
			result = self.const(result)
		
		return result, dividend
	'''
	
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
	
	__all__ = __all__ + ('test_polynomial', 'test_optimization', 'polynomial_test_suite')


if __debug__ and __name__ == '__main__':
	'''
	p = Polynomial.get_algebra(base_ring=BooleanRing.get_algebra())
	one = p.one()
	x = p.var('x')
	y = p.var('y')
	z = p.var('z')
	
	a = x * y + x * z + y
	b = x * y + y + one

	d, r = divmod(a, b)

	assert d * b + r == a

	print(f"({d.canonical()}) * ({b.canonical()}) + {r.canonical()} == {a.canonical()}")
	quit()

	#test_optimization(Polynomial.get_algebra(base_ring=BooleanRing.get_algebra()), verbose=True)
	'''
	
	polynomial_test_suite(verbose=True)
	
	quit()
	
	from pathlib import Path
	from itertools import product
	from jit_types import Compiler
	
	compiler = Compiler()
	
	RijndaelField.compile_tables('RijndaelField', compiler)
	assert hasattr(RijndaelField, 'jit_log_table')
	assert hasattr(RijndaelField, 'jit_exp_table')
	
	#polynomial = Polynomial.get_algebra(base_ring=ModularRing.get_algebra(size=301))
	#polynomial = Polynomial.get_algebra(base_ring=BooleanRing.get_algebra())
	polynomial = Polynomial.get_algebra(base_ring=RijndaelField.get_algebra())
	#polynomial = Polynomial.get_algebra(base_ring=BinaryField.get_algebra(exponent=2, reducing_polynomial_bitfield=0b111))
	var_list = 'abcdefgh'
	v = list(map(polynomial.var, var_list))
	p1 = polynomial.random(variables=v, order=7)
	p1 = p1.optimized()
	p1.compile('p1', compiler)
	#print(p1)
	
	#print(compiler)
	
	code = compiler.compile()
	
	p1c = p1.wrap_compiled('p1', code)
	#Path('polynomial.bc').write_bytes(code.modules[0].as_bitcode())
	
	#log_table, exp_table = RijndaelField.log_exp_tables()
	#print(log_table)
	#print(exp_table)
	#for n in range(1, 256):
	#	assert exp_table[log_table[n]] == n, str(n)
	
	#va = polynomial.base_ring.random()
	#vb = polynomial.base_ring.random()
	#va = polynomial.base_ring(178)
	#vb = polynomial.base_ring(1)
	#try:
	#	print("py", va.log(), vb.log(), int(polynomial.base_ring.exp((va.log() + vb.log()) % (polynomial.base_ring.size - 1))))
	#	print("ll", log_table[int(va)], log_table[int(vb)], exp_table[(log_table[int(va)] + log_table[int(vb)]) % (polynomial.base_ring.size - 1)])
	#except ZeroDivisionError:
	#	pass
	#print("py", int(va), "*", int(vb), "=", int(p1(a=va, b=vb).evaluate()))
	#print("ll", int(va), "*", int(vb), "=", int(p1c(a=va, b=vb)))
	
	with code:
		for vs in range(100):
			args = dict((_v, polynomial.base_ring.random()) for _v in var_list)
			assert p1(**args).evaluate() == p1c(**args)







