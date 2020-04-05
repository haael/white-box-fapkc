#!/usr/bin/python3
#-*- coding:utf8 -*-

"Polynomials of rings or fields."

from enum import Enum
from itertools import chain, product
from collections import defaultdict, Counter, deque
from functools import reduce
import operator

from utils import Immutable, random_sample, parallel_map, parallel_starmap, canonical, evaluate, substitute
from algebra import Algebra, AlgebraicStructure
from rings import BooleanRing


__all__ = 'Polynomial',


class Polynomial(Immutable, AlgebraicStructure):
	"Polynomials over rings and fields."
	
	canonical_caching = True # optimization: if True, results of `canonical()` will be memoized
	variables_threshold = -1
	
	symbol = Enum('Polynomial.symbol', 'var const add sub neg mul')
	
	default_ring = BooleanRing.get_algebra()
	
	algebra_kwparams_names = 'base_ring',
	
	def __init__(self, operator, operands=None, base_ring=None):
		if operands == None:
			try:
				operands = operator.operands
				operator = operator.operator
			except AttributeError:
				operands = [base_ring(operator)]
				operator = self.symbol.const
		
		if __debug__: len(operands) # cause TypeError if `operands` is not iterable
		
		if operator != self.symbol.var and operator != self.symbol.const:
			try:
				if base_ring != None:
					algebra = self.get_algebra(base_ring=base_ring)
				else:
					algebra = operands[0].algebra
				
				if algebra.algebra_name != 'Polynomial':
					raise ValueError("Constants not allowed outside of the `const` container.")
				
				if any(_op.algebra != algebra for _op in operands[1:]):
					raise ValueError("All operands must be from the same ring: {}.".format(operands))
			except IndexError:
				pass
		
		assert len(operands) == 2 if operator == self.symbol.var else True
		assert isinstance(operands[0], str) if operator == self.symbol.var else True
		assert isinstance(operands[1], Algebra) if operator == self.symbol.var else True
		
		#print(operands)
		assert all(isinstance(_op, Polynomial) for _op in operands) if (operator != self.symbol.const and operator != self.symbol.var) else True
		
		self.operator = operator
		assert isinstance(operands, list)
		self.operands = operands
		
		assert self.algebra.algebra_name == 'Polynomial'
		
		if base_ring != None and self.algebra.base_ring != base_ring:
			raise ValueError("`base_ring` = {} does not match operand algebra {}.".format(base_ring, self.algebra))
		
		self.mutable.add('is_canonical')
		self.mutable.add('canonical_cache')
		self.mutable.add('variables_cache')
		self.is_canonical = False
		self.immutable = True
	
	def __getnewargs_ex__(self):
		return (self.operator, self.operands), {'base_ring':self.algebra.base_ring}
	
	@property
	def algebra(self):
		if self.operator == self.symbol.var:
			base_ring = self.operands[1]
		elif self.operator == self.symbol.const:
			try:
				base_ring = self.operands[0].algebra
			except IndexError:
				base_ring = self.default_ring
		else:
			algebra = self.operands[0].algebra
			if algebra.algebra_name == 'Polynomial':
				return algebra
			else:
				base_ring = algebra
		
		return self.get_algebra(base_ring=base_ring)
	
	@classmethod
	def var(cls, name, base_ring):
		result = cls(cls.symbol.var, [name, base_ring], base_ring=base_ring)
		result.is_canonical = True
		return result
	
	@classmethod
	def const(cls, value, base_ring=None):
		if hasattr(value, 'operator') and hasattr(value, 'operands'):
			raise TypeError("Const value must not be a polynomial.")
		
		if value or value.algebra != cls.default_ring:
			result = cls(cls.symbol.const, [value.canonical()], base_ring=base_ring)
		else:
			result = cls(cls.symbol.const, [], base_ring=base_ring)
		result.is_canonical = True
		return result
	
	@classmethod
	def zero(cls, base_ring=default_ring):
		return cls.const(base_ring.zero())
	
	@classmethod
	def one(cls, base_ring=default_ring):
		return cls.const(base_ring.one())
	
	@classmethod
	def random(cls, variables=None, order=0, base_ring=default_ring):
		algebra = cls.get_algebra(base_ring=base_ring)
		
		if variables == None:
			variables = []
		
		ds = []
		for n in range(order + 1):
			vs = list(random_sample(variables, len(variables), n))
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
			vs = list(random_sample(variables, len(variables), n))
			vs.append(algebra.const(base_ring.random()))
			monomial = algebra(cls.symbol.mul, vs)
			ds.append(monomial)
		
		result = algebra(cls.symbol.add, ds).canonical()
		if not result: result += base_ring.random_nonzero()
		
		return result
	
	#def minimal(self):
	#	(a + b) * (c + d) = a * c + a * d + b * c + b * d
	
	def canonical(self):
		"Return algebraic normal form of this polynomial. Two polynomials are equal everywhere if their algebraic normal forms are identical."
		
		if self.is_canonical:
			return self
		elif hasattr(self, 'canonical_cache'):
			assert self.canonical_cache.is_canonical
			return self.canonical_cache
		elif self.operator == self.symbol.var:
			self.is_canonical = True
			return self
		elif self.operator == self.symbol.const:
			assert len(self.operands) <= 1
			if self.is_zero():
				#print("zero canonical")
				result = self.algebra.zero()
				result.is_canonical = True
				if self.canonical_caching: self.canonical_cache = result
				return result
			else:
				self.is_canonical = True
				return self
		elif self.operator == self.symbol.neg:
			assert len(self.operands) == 1
			if self.algebra.base_ring.size == 2:
				result = self.operands[0].canonical()
				if self.canonical_caching: self.canonical_cache = result
				return result
			else:
				result = ((-self.algebra.base_ring.one()) * self.operands[0].canonical()).canonical()
				if self.canonical_caching: self.canonical_cache = result
				return result
		elif self.operator == self.symbol.sub:
			assert len(self.operands) == 2
			return (self.operands[0].canonical() + ((-self.operands[1]).canonical())).canonical()
		elif self.operator == self.symbol.add or self.operator == self.symbol.mul:
			base_ring = self.algebra.base_ring
			addends_before = deque([self])
			addends_after = []
			while addends_before:
				addend = addends_before.pop()
				if addend.operator == self.symbol.add:
					addends_before.extend(addend.operands)
				elif addend.operator == self.symbol.var or addend.operator == self.symbol.const:
					addends_after.append([addend])
				elif addend.operator == self.symbol.mul:
					factors_before = deque([addend])
					factors_after = []
					while factors_before:
						factor = factors_before.pop()
						if factor.operator == self.symbol.mul:
							factors_before.extend(factor.operands)
						elif factor.operator == self.symbol.const or factor.operator == self.symbol.var:
							factors_after.append(factor)
						elif factor.operator == self.symbol.add:
							for f in factor.operands:
								addends_before.append(self.__class__(self.symbol.mul, list(factors_before) + [f] + factors_after, base_ring))
							factors_before = factors_after = None
							break
						elif hasattr(factor, 'operator'):
							factors_before.append(factor.canonical())
						else:
							factors_after.append(self.const(factor.canonical()))
					
					if factors_after:
						addends_after.append(factors_after)
					elif factors_after != None:
						addends_after.append([self.algebra.one()])
				elif hasattr(addend, 'operator'):
					addends_before.append(addend.canonical())
				else:
					addends_after.append([self.const(addend.canonical())])
			
			addends_grouped = defaultdict(lambda: base_ring.zero())
			for addend in addends_after:
				assert isinstance(addend, list)
				
				constants = [(_f.operands[0] if _f.operands else base_ring.zero()) for _f in addend if _f.operator == self.symbol.const]
				variables = [_f for _f in addend if _f.operator == self.symbol.var]
				assert len(constants) + len(variables) == len(addend)
				
				if self.algebra.base_ring.size == 2:
					variables = list(set(variables))
				
				factor = base_ring.one()
				for c in constants:
					factor *= c
				
				if not factor.is_zero():
					monomial = tuple(sorted(variables, key=self.__class__.sort_ordering))
					addends_grouped[monomial] += factor
			
			del addends_after
			
			addends_sorted = []
			for monomial, factor in addends_grouped.items():
				assert isinstance(monomial, tuple)
				if not factor.is_zero() and ((not factor.is_one()) or (not monomial)):
					addends_sorted.append(self.__class__(self.symbol.mul, [self.const(factor)] + list(monomial), base_ring))
				elif factor.is_one():
					addends_sorted.append(self.__class__(self.symbol.mul, list(monomial), base_ring))
			addends_sorted.sort(key=self.__class__.sort_ordering)
			
			if len(addends_sorted) == 0:
				result = self.algebra.zero()
			elif len(addends_sorted) == 1:
				monomial = addends_sorted[0]
				if len(monomial.operands) == 1:
					result = monomial.operands[0]
					if result.operator == self.symbol.const and result.is_zero():
						result = self.algebra.zero()
				else:
					result = self.__class__(self.symbol.mul, addends_sorted[0].operands, base_ring)
			else:
				for addend in addends_sorted:
					addend.is_canonical = True
				result = self.__class__(self.symbol.add, addends_sorted, base_ring)
			
			#print("canonical:", str(result))
			result.is_canonical = True
			if self.canonical_caching: self.canonical_cache = result
			return result
			
			# new_operands = defaultdict(lambda: self.algebra.base_ring.zero())
			# if self.operator == self.symbol.mul:
				# new_operands[tuple()] = self.algebra.base_ring.one()
			
			# for operand in parallel_map(canonical, self.operands):
				# assert isinstance(operand, Polynomial)
				# assert operand.is_canonical
				
				# ovl_operands = defaultdict(lambda: self.algebra.base_ring.zero())
				
				# for monomial in operand:
					# if monomial.operator == self.symbol.mul:
						# if monomial.operands[0].operator == self.symbol.const:
							# try:
								# factor = monomial.operands[0].operands[0]
							# except IndexError:
								# factor = self.algebra.base_ring.zero()
							# variables = tuple(monomial.operands[1:])
						# else:
							# factor = self.algebra.base_ring.one()
							# variables = tuple(monomial.operands)
					# elif monomial.operator == self.symbol.const:
						# try:
							# factor = monomial.operands[0]
							# variables = tuple()
						# except IndexError:
							# factor = self.algebra.base_ring.zero()
							# variables = tuple()
					# elif monomial.operator == self.symbol.var:
						# factor = self.algebra.base_ring.one()
						# variables = (monomial,)
					# else:
						# raise RuntimeError
					
					# ovl_operands[variables] = factor
				
				# if self.operator == self.symbol.add:
					# for variables, factor in ovl_operands.items():
						# new_operands[variables] += factor
				# elif self.operator == self.symbol.mul:
					# old_operands = new_operands
					# new_operands = defaultdict(lambda: self.algebra.base_ring.zero())
					# for (variables_o, factor_o), (variables_v, factor_v) in product(old_operands.items(), ovl_operands.items()):
						# if self.algebra.base_ring.size == 2: # x * x == x
							# variables_n = frozenset(variables_o + variables_v)
						# else:
							# variables_n = variables_o + variables_v
						# new_operands[tuple(sorted(variables_n, key=self.__class__.sort_ordering))] += factor_o * factor_v
				# else:
					# raise RuntimeError
			
			# unsorted_operands = list(new_operands.keys())
			# for n, monomial in enumerate(unsorted_operands):
				# factor = new_operands[monomial]
				# if factor.is_zero():
					# unsorted_operands[n] = None
				# elif len(monomial) == 0:
					# unsorted_operands[n] = self.algebra.const(factor)
					# unsorted_operands[n].is_canonical = True
				# elif factor.is_one():
					# if len(monomial) == 1:
						# unsorted_operands[n] = monomial[0]
						# unsorted_operands[n].is_canonical = True
					# else:
						# unsorted_operands[n] = self.algebra(self.symbol.mul, list(monomial))
						# unsorted_operands[n].is_canonical = True
				# else:
					# unsorted_operands[n] = self.algebra(self.symbol.mul, list((self.algebra.const(factor),) + monomial))
					# unsorted_operands[n].is_canonical = True
			
			# sorted_operands = sorted((_monomial for _monomial in unsorted_operands if _monomial != None), key=self.__class__.sort_ordering)
			
			# if len(sorted_operands) == 0:
				# result = self.algebra.zero()
			# elif len(sorted_operands) == 1:
				# result = sorted_operands[0]
			# else:
				# result = self.algebra(self.symbol.add, sorted_operands)
			# result.is_canonical = True
			# if self.canonical_caching: self.canonical_cache = result
			# return result




		else:
			raise RuntimeError
	
	def sort_ordering(self):
		"String returned here affects the ordering of terms in `canonical`."
		if self.operator == self.symbol.var:
			return "3_999_" + self.operands[0]
		elif self.operator == self.symbol.const:
			if self.operands:
				return self.operands[0].sort_ordering()
			else:
				return self.algebra.base_ring.zero().sort_ordering()
		else:
			return "0xx4523"[self.operator.value] + "_" + "{:04d}".format(1000 - len(self.operands)) + "_".join(_operand.sort_ordering() for _operand in self.operands)
	
	@classmethod
	def __optional_parentheses(cls, term):
		try:
			if term.operator in (cls.symbol.add, cls.symbol.sub, cls.symbol.mul):
				return "(" + str(term) + ")"
			else:
				return str(term)
		except AttributeError:
			return str(term)
	
	def __repr__(self):
		return ''.join(['<', self.__class__.__qualname__, ': ', str(self.operator), ', ', repr(self.operands), '>'])
	
	def __str__(self):
		if self.operator == self.symbol.var:
			return self.operands[0]
		elif self.operator == self.symbol.const:
			return str(self.operands[0]) if self.operands else str(self.algebra.base_ring.zero())
		elif self.operator == self.symbol.neg:
			return "-" + self.__optional_parentheses(self.operands[0])
		elif self.operator == self.symbol.sub:
			return self.__optional_parentheses(self.operands[0]) + " - " + self.__optional_parentheses(self.operands[1])
		elif self.operator == self.symbol.add:
			return " + ".join(self.__optional_parentheses(_op) for _op in self.operands)
		elif self.operator == self.symbol.mul:
			return " * ".join(self.__optional_parentheses(_op) for _op in self.operands)
		else:
			raise RuntimeError("Usupported operator trying to convert polynomial to string.")
	
	def __bool__(self):
		c = self.canonical()
		if c.operator == self.symbol.const:
			try:
				return bool(c.operands[0])
			except IndexError:
				return False
		else:
			return True
	
	def __hash__(self):
		if not hasattr(self, 'operator'): return 0 # unpickle protocol
		
		if __debug__: super().__hash__() # ensure the object has been initialized properly
		
		if self.operator == self.symbol.var:
			return hash(self.operands[0])
		elif self.operator == self.symbol.const:
			if self.operands:
				return hash(self.operands[0])
			else:
				return hash(self.algebra.base_ring.zero())
		elif self.is_canonical and self.operator == self.symbol.mul:
			return reduce(operator.mul, (hash(_op) for _op in self.operands))
		elif self.is_canonical and self.operator == self.symbol.add:
			return sum((hash(_op) for _op in self.operands))
		else:
			raise ValueError("Only Polynomial literals and canonical polynomials can be hashed.")
	
	def variables(self):
		try:
			return self.variables_cache
		except AttributeError:
			if self.operator == self.symbol.const:
				result = frozenset()
			elif self.operator == self.symbol.var:
				result = frozenset([self])
			else:
				result = frozenset().union(*[_op.variables() for _op in self.operands])
			self.variables_cache = result
			return result
	
	def __eq__(self, other):
		if self is other:
			return True
		
		try:
			if self.operator == other.operator == self.symbol.var: # optimization
				return self.operands == other.operands
		except AttributeError:
			pass
		
		if not hasattr(other, 'canonical'):
			return NotImplemented
		
		try:
			variables = self.variables() | other.variables()
			other_is_const = False
		except AttributeError:
			variables = self.variables()
			other_is_const = True
		
		#print("compare", self, other)
		
		if len(variables) * self.algebra.base_ring.size > self.variables_threshold:
			#print("case A")
			if not hasattr(other, 'operator'):
				other_canonical = self.const(other).canonical()
			else:
				other_canonical = other.canonical()
			
			self_canonical = self.canonical()
			
			#print("self:", self.operator, self.operands)
			#print("self_canonical:", self_canonical.operator, self_canonical.operands)
			#print("other:", other.operator, other.operands)
			#print("other_canonical:", other_canonical.operator, other_canonical.operands)
			
			try:
				return self_canonical.operator == other_canonical.operator and self_canonical.operands == other_canonical.operands		
			except AttributeError:
				return NotImplemented
		elif other_is_const:
			#print("case B")
			for valuation in valuations(*variables):
				if self(**valuation).evaluate() != other:
					return False
			else:
				return True
		else:
			#print("case C")
			for valuation in valuations(*variables):
				if self(**valuation).evaluate() != other(**valuation).evaluate():
					return False
			else:
				return True
	
	def __gt__(self, other):
		return self.evaluate() > other.evaluate()
	
	def __add__(self, other):
		if other.algebra != self.algebra:
			other = self.algebra.const(other)
		if self.operator == other.operator == self.symbol.add:
			return self.algebra(self.symbol.add, self.operands + other.operands)
		else:
			return self.algebra(self.symbol.add, [self, other])
	
	def __radd__(self, other):
		if other.algebra != self.algebra:
			other = self.algebra.const(other)
		if self.operator == other.operator == self.symbol.add:
			return self.algebra(self.symbol.add, other.operands + self.operands)
		else:
			return self.algebra(self.symbol.add, [other, self])
	
	def __sub__(self, other):
		if other.algebra != self.algebra:
			other = self.algebra.const(other)
		return self.algebra(self.symbol.sub, [self, other])
	
	def __rsub__(self, other):
		if other.algebra != self.algebra:
			other = self.algebra.const(other)
		return self.algebra(self.symbol.sub, [other, self])
	
	def __neg__(self):
		return self.algebra(self.symbol.neg, [self])
	
	def __mul__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		if self.operator == other.operator == self.symbol.mul:
			return self.algebra(self.symbol.mul, self.operands + other.operands)
		else:
			return self.algebra(self.symbol.mul, [self, other])
	
	def __rmul__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		if self.operator == other.operator == self.symbol.mul:
			return self.algebra(self.symbol.mul, other.operands + self.operands)
		else:
			return self.algebra(self.symbol.mul, [other, self])
	
	@staticmethod
	def __monomial_division(dividend, divisor):
		if not dividend.is_canonical:
			raise ValueError("Dividend must be in a canonical form.")
		if not divisor.is_canonical:
			raise ValueError("Divisor must be in a canonical form.")
		
		if dividend.operator not in [dividend.symbol.mul, dividend.symbol.const, dividend.symbol.var]:
			raise ValueError("Dividend is not a monomial.")
		if divisor.operator not in [divisor.symbol.mul, divisor.symbol.const, divisor.symbol.var]:
			raise ValueError("Divisor is not a monomial.")
		
		assert dividend.algebra == divisor.algebra
		
		Ring = dividend.algebra.base_ring
		
		dividend_vars = Counter()
		if dividend.operator == dividend.symbol.mul:
			if dividend.operands[0].operator == dividend.symbol.const:
				dividend_factor = dividend.operands[0].operands[0]
				for v in dividend.operands[1:]:
					assert v.operator == dividend.symbol.var
					dividend_vars[v] += 1
			else:
				dividend_factor = Ring.one()
				for v in dividend.operands:
					assert v.operator == dividend.symbol.var
					dividend_vars[v] += 1
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
					assert v.operator == divisor.symbol.var
					divisor_vars[v] += 1
			else:
				divisor_factor = Ring.one()
				for v in divisor.operands:
					assert v.operator == divisor.symbol.var
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
		return result.canonical()
	
	@staticmethod
	def __monomial_order(monomial):
		if not monomial.is_canonical:
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
		else:
			try:
				divisor = other.canonical()
			except AttributeError:
				return NotImplemented
		
		dividend = self.canonical()
		
		assert dividend.algebra == divisor.algebra
		
		Ring = self.algebra
		
		try:
			d = next(iter(divisor)) # leading term of the divisor
		except TypeError:
			d = self.const(divisor)
		except StopIteration:
			raise ZeroDivisionError("Division by zero in polynomial Euclidean division.")
		
		if not dividend:
			return Ring.zero(), Ring.zero()
		
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
					dividend = dividend.canonical()
					running = bool(dividend)
					break
				except ArithmeticError:
					pass
			else:
				running = False
				pass
		
		if not hasattr(result, 'operator'):
			result = self.const(result)
		
		return result.canonical(), dividend.canonical()
	
	def __rdivmod__(self, other):
		return divmod(self.const(other), self)
	
	def __truediv__(self, other):
		quotient, remainder = divmod(self, other)
		if remainder:
			raise ArithmeticError("Remainder nonzero when dividing polynomials.")
		return quotient
	
	def __rtruediv__(self, other):
		quotient, remainder = divmod(self.algebra.const(other), self)
		if remainder:
			raise ArithmeticError("Remainder nonzero when dividing polynomials.")
		return quotient
	
	def __floordiv__(self, other):
		quotient, remainder = divmod(self, other)
		return quotient
	
	def __mod__(self, other):
		quotient, remainder = divmod(self, other)
		return remainder
	
	def __iter__(self):
		"As an iterator, yields the monomials that constitute the algebraic normal form. If the polynomial is 0, yields nothing."
		
		c = self.canonical()
		
		if c.operator == self.symbol.add:
			yield from c.operands
		elif c:
			yield c
	
	def __or__(self, other):
		"Return 'disjunction' of polynomials, defined as `x + y - x * y`."
		return self + other - self * other
	
	def __ror__(self, other):
		"Return 'disjunction' of polynomials, defined as `x + y - x * y`. Reversed method.  "
		return other + self - other * self
	
	def __call__(self, **kwargs):
		"Substitute variables in the polynomial with the values provided in keyword arguments. Variables are matched by name with the argument names."
		
		if not kwargs:
			return self
		
		s_vars = frozenset(kwargs.keys())
		
		if self.operator == self.symbol.const:
			return self
		elif self.operator == self.symbol.var:
			try:
				result = kwargs[self.operands[0]]
				if (result.algebra != self.algebra) and (self.algebra.base_ring != result.algebra):
					raise ValueError("Substituted value must be from the same algebra as the original polynomial. ({} vs. {})".format(str(self.algebra), str(result.algebra)))
				if hasattr(result, 'operator'):
					return result
				else:
					return self.const(result)
			except KeyError:
				return self
		elif not (frozenset(str(_v) for _v in self.variables()) & s_vars):
			return self
		else:
			return self.algebra(self.operator, list(parallel_starmap(substitute, [(_op, self.algebra, kwargs) for _op in self.operands])))
			#return self.algebra(self.operator, [(_op(**kwargs) if hasattr(_op, 'operator') else self.const(_op)) for _op in self.operands])
	
	def __pow__(self, exponent):
		if (not self) and (not exponent):
			raise ZeroDivisionError("Zero to the power of zero.")
					
		if not self:
			return self.algebra.zero()
		
		if exponent >= 0:
			base = self
		else:
			base = self.algebra.one() / self
		
		result = self.algebra.one()
		
		for i in range(abs(exponent)):
			result *= base
		
		return result
	
	def is_zero(self):
		return self.evaluate().is_zero()
	
	def is_one(self):
		return self.evaluate().is_one()
	
	@classmethod
	def domain(cls, base_ring=default_ring):
		algebra = cls.get_algebra(base_ring=base_ring)
		for value in base_ring.domain():
			yield algebra(value)
	
	def evaluate(self):
		if self.operator == self.symbol.const:
			try:
				return self.operands[0]
			except IndexError:
				return self.algebra.base_ring.zero()
		elif self.operator == self.symbol.var:
			raise ValueError("Only ground polynomials (without variables) can be evaluated to a constant. (found var: `{}`)".format(self.operands))
		elif self.operator == self.symbol.add:
			result = self.algebra.base_ring.zero()
			for operand in parallel_map(evaluate, self.operands):
				if not operand.is_zero():
					result += operand
			return result
		elif self.operator == self.symbol.mul:
			if any((not hasattr(_op, 'operator') or _op.operator == self.symbol.const) and _op.is_zero() for _op in self.operands):
				return self.algebra.base_ring.zero()
			result = self.algebra.base_ring.one()
			for operand in parallel_map(evaluate, self.operands):
				if operand.is_zero():
					return self.algebra.base_ring.zero()
				elif not operand.is_one():
					result *= operand
			return result
		elif self.operator == self.symbol.sub:
			assert len(self.operands) == 2
			return self.operands[0].evaluate() - self.operands[1].evaluate()
		elif self.operator == self.symbol.neg:
			assert len(self.operands) == 1
			return -self.operands[0].evaluate()
		else:
			raise RuntimeError("Unsupported operator: {}.".format(str(self.operator)))
	
	@property
	def ring_value(self):
		c = self.evaluate()
		assert c.algebra.algebra_name != 'Polynomial'
		assert c.algebra == self.algebra.base_ring
		return c.ring_value
	
	def __int__(self):
		return int(self.evaluate())


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
		
		assert pickle.loads(pickle.dumps(x)) == x
		assert pickle.loads(pickle.dumps(x + y)) == x + y
		
		p_a = x * y
		p_b = pickle.dumps(x * y)
		p_c = pickle.loads(p_b)
		assert p_a == p_c
		
		assert pickle.loads(pickle.dumps(x * y)) == x * y
		
		assert x == x
		assert y == y
		assert z == z

		assert x != y
		assert x != z
		assert y != x
		assert y != z
		assert z != x
		assert z != y
		
		#print((x + y).canonical())
		#print(((x + y) * (x + y)).canonical())
		#print(((x + y) * (x + y) * (x + y)).canonical())
		
		assert (x + y) * (x - y) == x**2 - y**2
		assert (x + y) * (x + y) == x**2 + x * y + x * y + y**2
		assert (x + y) * (x + y) * (x + y) == x**3 + x**2 * y + x**2 * y + x**2 * y + x * y**2 + x * y**2 + x * y**2 + y**3
		
		assert x // x == yes
		assert x // y == no
		assert y // x == no
		assert y // y == yes
		
		assert (x * x) // (y) == no
		assert (x * x) // (x * x) == yes
		assert (x * y) // (y * x) == yes
		assert (x * x + y) // (x * x) == yes
		assert (x * x + y) // (y + x * x) == yes
		
		assert (x * y)(x=yes, y=no) == no
		assert (x * y)(x=yes, y=yes) == yes
		assert (x + y)(x=yes, y=no) == yes
		assert (x * y + x)(x=z) == (z * y + z)
		assert (x * y + x)(x=y) == no if x**2 + x == no else True
		assert (x * y)(x=z, y=z) == z if x**2 == x else True
		
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
			assert a - a == no
			assert -a == (-yes) * a
			assert yes * a == a * yes == a
			assert no * a == a * no == no
			assert yes | a == a | yes == yes
			assert no | a == a | no == a
			assert a // yes == a
			
			assert a**1 == a
			
			try:
				assert a**0 == yes
			except ZeroDivisionError:
				assert not a
			except ArithmeticError:
				assert yes % a
			
			try:
				assert (a**-1 == yes // a) or (yes % a)
			except ZeroDivisionError:
				assert not a
			except ArithmeticError:
				assert yes % a

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
			
		
		sample1 = random_sample(iter(field_samples), len(field_samples), test_size)
		sample2 = random_sample(iter(field_samples), len(field_samples), test_size)
		for n, (a, b) in enumerate(random_sample(product(sample1, sample2), test_size**2, test_size)):
			assert a + b == b + a
			assert a * b == b * a
			assert a - b == a + (-b) == -b + a
			assert (-a) * b == a * (-b) == -(a * b)
			assert (-a) * (-b) == a * b
			
			try:
				q, r = divmod(a, b)
				assert q * b + r == a
				
				assert q == a // b
				assert r == a % b
			except ZeroDivisionError:
				assert not b
		
		sample1 = random_sample(iter(field_samples), len(field_samples), test_size)
		sample2 = random_sample(iter(field_samples), len(field_samples), test_size)
		sample3 = random_sample(iter(field_samples), len(field_samples), test_size)
		for n, (a, b, c) in enumerate(random_sample(product(sample1, sample2, sample3), test_size**3, test_size)):
			assert (a + b) + c == a + (b + c)
			assert (a + b) * c == a * c + b * c
			assert (a - b) * c == a * c - b * c
		
		'''
		print(1, x.canonical())
		print(2, y.canonical())
		print(3, (x + y + no).canonical())
		print(4, (yes + x * y + x + y).canonical())
		print(5, (yes * x).canonical())
		print(6, (no + y).canonical())
		'''
		
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
		
		ring = BooleanRing.get_algebra()
		if verbose: print()
		if verbose: print("test Polynomial(base_ring=BooleanRing())")
		ring_polynomial = Polynomial.get_algebra(base_ring=ring)
		if verbose: print(" ring test")
		test_ring(ring_polynomial)
		if verbose: print(" polynomial test")
		test_polynomial(ring_polynomial)
		
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
	
	__all__ = __all__ + ('test_polynomial', 'polynomial_test_suite')


if __debug__ and __name__ == '__main__':
	polynomial_test_suite(verbose=True)



