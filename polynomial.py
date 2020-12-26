#!/usr/bin/python3
#-*- coding:utf8 -*-

"Polynomials of rings or fields."

from enum import Enum
from itertools import chain, product
from collections import defaultdict, Counter, deque
from functools import reduce
import operator

from utils import Immutable, random_sample, parallel_map, parallel_starmap, canonical, optimized, evaluate, substitute
from algebra import Algebra, AlgebraicStructure
from rings import BooleanRing

from math import log10, ceil


__all__ = 'Polynomial',


class AllowCanonical:
	def __enter__(self):
		Polynomial.allow_canonical += 1
	
	def __exit__(self, *args):
		Polynomial.allow_canonical -= 1


class Polynomial(Immutable, AlgebraicStructure):
	"Polynomials over rings and fields."
	
	allow_canonical = 1 # if 0, using `canonical()` is not allowed
	canonical_caching = True # optimization: if True, results of `canonical()` will be memoized
	optimized_caching = True # optimization: if True, results of `optimized()` will be memoized
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
		
		if __debug__: len(operands) # raise TypeError if `operands` is not iterable
		
		if operator != self.symbol.var and operator != self.symbol.const:
			try:
				if base_ring != None:
					algebra = self.get_algebra(base_ring=base_ring)
				else:
					algebra = operands[0].algebra
				
				if algebra.algebra_name != 'Polynomial':
					raise ValueError("Constants not allowed outside of the `const` container.")
				
				#print("operator", operator, "operands", operands)
				
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
		self.mutable.add('is_optimized')
		self.mutable.add('optimized_cache')
		self.mutable.add('variables_cache')
		self.mutable.add('circuit_size_cache')
		self.is_canonical = False
		self.is_optimized = False
		self.immutable = True
		self.circuit_size_cache = None
		
		# This is a very expensive check.
		#assert self.is_valid_polynomial(), repr(self)
	
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
		result.is_optimized = True
		return result
	
	@classmethod
	def const(cls, value, base_ring=None):
		if hasattr(value, 'operator') and hasattr(value, 'operands'):
			raise TypeError("Const value must not be a polynomial.")
		
		if not hasattr(value, 'algebra'):
			value = base_ring(value)
		
		if (hasattr(value, 'ring_value') and hasattr(value.ring_value, 'jit_value')) or value or value.algebra != cls.default_ring:
			result = cls(cls.symbol.const, [value], base_ring=base_ring)
		else:
			result = cls(cls.symbol.const, [], base_ring=base_ring)
		
		result.is_canonical = True
		result.is_optimized = True
		return result
	
	@classmethod
	def zero(cls, base_ring=default_ring):
		return cls.const(base_ring.zero())
	
	@classmethod
	def one(cls, base_ring=default_ring):
		return cls.const(base_ring.one())
	
	@classmethod
	def sum(cls, addends, base_ring=default_ring):
		if len(addends) == 0:
			return cls.zero(base_ring=base_ring)
		elif len(addends) == 1:
			return addends[0]
		else:
			return cls(cls.symbol.add, addends, base_ring=base_ring)
	
	@classmethod
	def product(cls, factors, base_ring=default_ring):
		if len(factors) == 0:
			return cls.one(base_ring=base_ring)
		elif len(factors) == 1:
			return factors[0]
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
		
		result = algebra(cls.symbol.add, ds).canonical()
		if not result: result += base_ring.random_nonzero()
		
		return result
	
	def is_canonical_literal(self):
		return self.operator in (self.symbol.const, self.symbol.var)
	
	def is_canonical_monomial(self):
		if self.is_canonical_literal(): return True
		if self.operator != self.symbol.mul: return False
		if not all(_op.is_canonical_literal() for _op in self.operands): return False
		if any(_op.operator == self.symbol.const for _op in self.operands[1:]): return False
		#print([self.operands[_n].sort_ordering() for _n in range(len(self.operands))])
		if any(self.operands[_n].sort_ordering() > self.operands[_n + 1].sort_ordering() for _n in range(1, len(self.operands) - 1)): return False
		return True
	
	def is_canonical_polynomial(self):
		if self.is_canonical_monomial(): return True
		if self.operator != self.symbol.add: return False
		if not all(_op.is_canonical_monomial() for _op in self.operands): return False
		if any(_op.operator == self.symbol.const for _op in self.operands[:-1]): return False
		if any(self.operands[_n].sort_ordering() >= self.operands[_n + 1].sort_ordering() for _n in range(len(self.operands) - 1)): return False
		return True
	
	def is_multiplicative_normal_form(self):
		if self.is_canonical_monomial(): return True
		if self.operator != self.symbol.mul: return False
		if any(_op.operator == self.symbol.const for _op in self.operands[:-1]): return False
		if any(_op.operator == self.symbol.mul for _op in self.operands): return False
		for operand in self.operands:
			if operand.operator == self.symbol.add and not operand.is_multiplicative_normal_form():
				return False
		return True
	
	def is_valid_polynomial(self):
		algebra = self.algebra
		base_ring = algebra.base_ring
		if self.operator == self.symbol.var:
			if len(self.operands) != 2:
				return False
			name, ring = self.operands
			if ring != base_ring:
				return False
			return True
		elif self.operator == self.symbol.const:
			if len(self.operands) == 0:
				return base_ring == self.default_ring
			elif len(self.operands) == 1:
				return self.operands[0].algebra == base_ring
			else:
				return False
		elif self.operator == self.symbol.add or self.operator == self.symbol.mul:
			return all(operand.is_valid_polynomial() and operand.algebra == algebra for operand in self.operands)
		elif self.operator == self.symbol.neg:
			if len(self.operands) != 1:
				return False
			return all(operand.is_valid_polynomial() and operand.algebra == algebra for operand in self.operands)
		elif self.operator == self.symbol.sub:
			if len(self.operands) != 2:
				return False
			return all(operand.is_valid_polynomial() and operand.algebra == algebra for operand in self.operands)
		else:
			return False
	
	def canonical(self):
		"Return algebraic normal form of this polynomial. Two polynomials are equal everywhere if their algebraic normal forms are identical. This function may take exponential time to finish."
		
		if not self.allow_canonical:
			raise RuntimeError("Using `canonical()` not allowed.")
		
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
								addends_before.append(self.algebra.product(list(factors_before) + [f] + factors_after))
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
				assert all(_factor.operator in (self.symbol.const, self.symbol.var) for _factor in monomial)
				if factor.is_zero():
					pass
				elif len(monomial) == 0:
					addends_sorted.append(self.const(factor))
				elif factor.is_one() and len(monomial) > 1:
					addends_sorted.append(self.algebra.product(list(monomial)))
				elif factor.is_one() and len(monomial) == 1:
					addends_sorted.append(monomial[0])
				else:
					addends_sorted.append(self.algebra.product([self.const(factor)] + list(monomial)))
			addends_sorted.sort(key=self.__class__.sort_ordering)
			
			if len(addends_sorted) == 0:
				result = self.algebra.zero()
			elif len(addends_sorted) == 1:
				monomial = addends_sorted[0]
				if monomial.operator in (self.symbol.const, self.symbol.var):
					result = monomial
				elif len(monomial.operands) == 1:
					result = monomial.operands[0]
					if result.operator == self.symbol.const and result.is_zero():
						result = self.algebra.zero()
				else:
					result = self.algebra.product(addends_sorted[0].operands)
			else:
				for addend in addends_sorted:
					addend.is_canonical = True
				result = self.algebra.sum(addends_sorted)
			
			assert result.operator in (self.symbol.mul, self.symbol.add, self.symbol.const, self.symbol.var), repr(result)
			assert len(result.operands) > 1 if result.operator in (self.symbol.add, self.symbol.mul) else True, repr(result)
			assert all(_addend.operator in (self.symbol.mul, self.symbol.const, self.symbol.var) for _addend in result.operands) if result.operator == self.symbol.add else True, repr(result)
			assert all(len(_addend.operands) > 1 for _addend in result.operands if _addend.operator == self.symbol.mul) if result.operator == self.symbol.add else True, repr(result)
			assert all(all(_factor.operator in (self.symbol.const, self.symbol.var) for _factor in _addend.operands) for _addend in result.operands if _addend.operator == self.symbol.mul) if result.operator == self.symbol.add else True, repr(result)
			assert all(all(_factor.operator == self.symbol.var for _factor in _addend.operands[1:]) for _addend in result.operands if _addend.operator == self.symbol.mul) if result.operator == self.symbol.add else True, repr(result)
			assert all(_factor.operator in (self.symbol.const, self.symbol.var) for _factor in result.operands) if result.operator == self.symbol.mul else True, repr(result)
			
			result.is_canonical = True
			if self.canonical_caching: self.canonical_cache = result
			return result
		else:
			raise RuntimeError
	
	def circuit_depth(self):
		if self.operator in [self.symbol.var, self.symbol.const]:
			return 0
		elif self.operator in [self.symbol.add, self.symbol.sub, self.symbol.mul]:
			return 1 + max(_operand.circuit_depth() for _operand in self.operands)
		elif self.operator in [self.symbol.neg]:
			return 1 + self.symbol.operands[0].circuit_depth()
		else:
			raise RuntimeError
	
	def circuit_width(self):
		if self.operator in [self.symbol.var, self.symbol.const]:
			return 1
		elif self.operator in [self.symbol.add, self.symbol.sub, self.symbol.mul]:
			return sum(_operand.circuit_width() for _operand in self.operands)
		elif self.operator in [self.symbol.neg]:
			return self.symbol.operands[0].circuit_width()
		else:
			raise RuntimeError
	
	def circuit_size(self):
		if self.circuit_size_cache != None:
			return self.circuit_size_cache
		
		if self.operator in [self.symbol.const]:
			self.circuit_size_cache = 0
			return 0
		elif self.operator in [self.symbol.var]:
			self.circuit_size_cache = 1
			return 1
		elif self.operator in [self.symbol.add, self.symbol.sub, self.symbol.mul]:
			self.circuit_size_cache = len(self.operands) + sum(_operand.circuit_size() for _operand in self.operands) - 1
			return self.circuit_size_cache
		elif self.operator in [self.symbol.neg]:
			self.circuit_size_cache = 1 + self.symbol.operands[0].circuit_size()
			return self.circuit_size_cache
		else:
			raise RuntimeError
	
	def is_identically_zero(self):
		try:
			return self.is_zero()
		except ValueError:
			return False
	
	def is_identically_one(self):
		try:
			return self.is_one()
		except ValueError:
			return False
	
	def evaluate_constants(self):
		if self.operator == self.symbol.add:
			addends = []
			constants = []
			for addend in self.operands:
				addend = addend.evaluate_constants()
				if addend.operator == self.symbol.const:
					constants.append(addend)
				else:
					addends.append(addend)
			constant = self.algebra.const(self.algebra.sum(constants).evaluate())
			if not addends:
				return constant
			if not constant.is_zero():
				addends.append(constant)
			
			if len(addends) == 1:
				return addends[0]
			else:
				return self.algebra.sum(addends)
		elif self.operator == self.symbol.mul:
			factors = []
			constants = []
			for factor in self.operands:
				factor = factor.evaluate_constants()
				if factor.operator == self.symbol.const:
					constants.append(factor)
				else:
					factors.append(factor)
			constant = self.algebra.const(self.algebra.product(constants).evaluate())
			if not factors:
				return constant
			if constant.is_zero():
				return self.algebra.zero()
			
			additive = [_n for (_n, _factor) in enumerate(factors) if _factor.operator == self.symbol.add]
			if len(additive) == 1:
				factor = factors[additive[0]]
				assert factor.operator == self.symbol.add
				del factors[additive[0]]
				added = self.algebra.sum([_addend * constant for _addend in factor.operands]).flatten()
				factors.append(added)
				return self.algebra.product(factors)
			
			if len(factors) == 1:
				factor = factors[0]
				if factor.operator == self.symbol.mul:
					return (factor * constant).flatten()
				else:
					return factor * constant
			
			if not constant.is_one():
				factors.append(constant)
			return self.algebra.product(factors)
		else:
			return self
	
	def flatten(self):
		if self.operator == self.symbol.add:
			operands = []
			for subterm in self.operands:
				operand = subterm.flatten()
				if operand.operator == self.symbol.add:
					operands.extend(operand.operands)
				else:
					operands.append(operand)
			
			return self.algebra.sum(sorted([_op for _op in operands if not _op.is_identically_zero()], key=self.__class__.sort_ordering)).evaluate_constants()
		elif self.operator == self.symbol.mul:
			operands = []
			for subterm in self.operands:
				operand = subterm.flatten()
				if operand.operator == self.symbol.mul:
					operands.extend(operand.operands)
				else:
					operands.append(operand)
			
			if any(_op.is_identically_zero() for _op in operands):
				return self.algebra.zero()
			else:
				return self.algebra.product(sorted([_op for _op in operands if not _op.is_identically_one()], key=self.__class__.sort_ordering)).evaluate_constants()
		
		elif self.operator == self.symbol.sub:
			left, right = self.operands
			return (left + (-right)).flatten()
		
		elif self.operator == self.symbol.neg:
			operand = self.operands[0]
			if operand.operator == self.symbol.neg:
				return operand.flatten()
			elif operand.operator == self.symbol.add:
				flat = operand.flatten()
				if flat.operator == self.symbol.add:
					return self.algebra.sum([-_addend for _addend in flat.operands]).flatten()
				else:
					return (-flat).flatten()
			elif operand.operator == self.symbol.const:
				try:
					return self.algebra.const((-operand.operands[1]).canonical())
				except IndexError:
					return self.algebra.zero()
			elif operand.operator in (self.symbol.var, self.symbol.mul):
				return (self.algebra.const((-self.algebra.one().operands[0]).canonical()) * operand).flatten()
			else:
				raise RuntimeError("Missed operation")
		else:
			return self
	
	def __optimize_additive_form(self):
		if self.operator == self.symbol.add:
			result_operands = []
			for operand in self.operands:
				if operand.symbol == self.symbol.add:
					result_operands.extend(operand.operands)
				else:
					result_operands.append(operand)
			
			if len(result_operands) == 0:
				return self.algebra.zero()
			elif len(result_operands) == 1:
				return result_operands[0]
			else:
				result_operands.sort(key=self.__class__.sort_ordering) # TODO?
				return self.algebra.sum(result_operands)
		elif self.operator == self.symbol.mul:
			result_factors = []
			for operand in self.operands:
				if operand.symbol == self.symbol.mul:
					result_factors.append([operand.operands])
				elif operand.symbol == self.symbol.add:
					result_factors.append(operand.operands)
				else:
					result_factors.append([operand])
			
			result_addends = [[]]
			for factors in result_factors:
				new_result_addends = []
				for old_addends in result_addends:
					new_result_addends.append(old_addends + factors)
				result_addends = new_result_addends
			
			for factors in result_addends:
				factors.sort(key=self.__class__.sort_ordering) # TODO?
			#result_addends.sort(key=self.__class__.sort_ordering) #TODO?
			
			return self.algebra.sum([self.algebra.product(_factor) for _factor in result_addends])
		elif self.operator == self.symbol.const:
			try:
				return self.algebra.const(self.operands[0].canonical())
			except IndexError: # boolean ring 0 value
				return self
		elif self.operator == self.symbol.var:
			return self
		elif self.operator == self.symbol.neg:
			return (self.algebra.const((-algebra.base_ring.one().operands[0]).canonical()) * self.operands[0]).__optimize_additive_form()
		elif self.operator == self.symbol.sub:
			assert len(self.operands) == 2
			return (self.operands[0].__optimize_additive_form() + ((-self.operands[1]).__optimize_additive_form())).__optimize_additive_form()
		else:
			raise RuntimeError
	
	class Identical:
		def __init__(self, term):
			self.term = term
		
		def __eq__(self, other):
			if self.term.operator != other.term.operator:
				return False
			
			if len(self.term.operands) != len(other.term.operands):
				return False
			
			if self.term.operator in (self.term.symbol.const, self.term.symbol.var):
				return self.term.operands == other.term.operands
			else:
				return all((Polynomial.Identical(_a) == Polynomial.Identical(_b)) for (_a, _b) in zip(self.term.operands, other.term.operands))
		
		def __hash__(self):
			if self.term.operator in (self.term.symbol.const, self.term.symbol.var):
				return hash(self.term)
			else:
				return hash((2938741, self.term.operator,) + tuple(self.term.Identical(_x) for _x in self.term.operands))
		
		def __str__(self):
			return str(self.term)
	
	def __optimize_traverse_subterms(self):
		if self.operator == self.symbol.add:
			candidate = self.algebra.sum([_subterm.__optimize_traverse_subterms() for _subterm in self.operands]).evaluate_constants()
		elif self.operator == self.symbol.mul:
			candidate = self.algebra.product([_subterm.__optimize_traverse_subterms() for _subterm in self.operands]).evaluate_constants()
		elif self.operator == self.symbol.sub:
			left, right = [_subterm.__optimize_traverse_subterms() for _subterm in self.operands]
			candidate = left - right
		else:
			return self
		
		return candidate
		#return self.__optimize_smallest(candidate.flatten().__optimize_additive_form().__optimize_equivalent_forms())
	
	def __optimize_smallest(self, terms):
		smallest = self
		smallest_size = smallest.circuit_size()
		for term in terms:
			term_size = term.circuit_size()
			#print("os:", term_size, term)
			if term_size < smallest_size:
				smallest = term
				smallest_size = term_size
		return smallest
	
	def __optimize_refactor(self):
		if self.operator != self.symbol.add:
			return self.algebra.one(), self
		
		factor_sets = []
		constant = self.algebra.one()
		for monomial in self.operands:
			factors = set()
			if monomial.operator == self.symbol.mul:
				for factor in monomial.operands:
					factors.add(self.Identical(factor))
			else:
				factors.add(self.Identical(monomial))
			factor_sets.append(factors)
		
		common_factors = frozenset().union(*factor_sets).intersection(*factor_sets)
		common_factor = self.algebra.product([_t.term for _t in common_factors])
		
		if common_factor.is_identically_zero():
			return self.algebra.one(), self.algebra.zero()
		elif common_factor.is_identically_one():
			return self.algebra.one(), self
		
		monomials = []
		for factor_set in factor_sets:
			monomials.append(self.algebra.product([_t.term for _t in factor_set - common_factors]))
		
		return common_factor, self.algebra.sum(monomials).flatten()
	
	def __optimize_equivalent_forms(self, depth=0):
		#print( "optimize_equivalent_forms", depth)
		if (self.operator != self.symbol.add) or len(self.operands) < 2 or depth >= 24: # <- optimization parameter
			yield self
			return
		
		pairs = []
		for m in random_sample(iter(range(len(self.operands))), len(self.operands), min(len(self.operands), 48)): # <- optimization parameter
			for n in random_sample(iter(range(m)), m, min(m, 8)): # <- optimization parameter
				s = self.operands[m]
				t = self.operands[n]
				
				f, c = (s + t).flatten().__optimize_refactor()
				if f.is_identically_one(): continue
				
				pairs.append((f, c, m, n))
		
		if not pairs:
			yield self
			return
		
		pairs.sort(key=lambda _t: _t[0].circuit_size())
		f, c, m, n = pairs[-1]
		r = self.algebra.sum([self.operands[_i] for _i in range(len(self.operands)) if _i not in (m, n)])
		equiv = f * c + r
		if equiv.circuit_size() < self.circuit_size():
			yield from equiv.flatten().__optimize_equivalent_forms(depth+1)
		else:
			yield self
	
	def __optimize_common_factors_old(self, depth=0):
		iteration = 0
		current = self
		while True:
			#print(" optimize_common_factors", depth, "*" * depth, iteration, current.circuit_size())
			if (self.operator != self.symbol.add) or len(self.operands) < 2:
				return current
			
			operands = list(current.operands)
			#operands.sort(key=lambda _o: _o.circuit_size())
			pairs = []
			for m in range(len(operands)):
				for n in range(m):
					s = operands[m]
					t = operands[n]
					
					f, c = (s + t).flatten().__optimize_refactor()
					if f.is_identically_one(): continue
					
					pairs.append((f, c, m, n))
			
			if not pairs:
				return current
			
			pairs.sort(key=lambda _t: _t[0].circuit_size())
			#print(len(pairs))
			f, c, m, n = pairs[-1]
			del pairs
			
			r = self.algebra.sum([operands[_i] for _i in range(len(operands)) if _i not in (m, n)])
			
			#equiv = (f * c + r).flatten()
			#if equiv.circuit_size() < current.circuit_size():
			#	current = equiv
			#	iteration += 1
			#	continue
			
			#f = f.flatten().__optimize_common_factors(depth+1)
			#c = c.flatten().__optimize_common_factors(depth+1)
			r = r.flatten().__optimize_common_factors(depth+1)
			#print(c)
			#print(r)

			equiv = (f * c + r).flatten()
			if equiv.circuit_size() < current.circuit_size():
				current = equiv
				iteration += 1
				continue
			
			return equiv
	
	def __optimize_common_factors(self, depth=0):
		iteration = 0
		current = self
		while True:
			#print(" optimize_common_factors", depth, "*" * depth, iteration, current.circuit_size())
			if (self.operator != self.symbol.add) or len(self.operands) < 2:
				return current
			
			operands = list(current.operands)
			#operands.sort(key=lambda _o: _o.circuit_size())
			pairs = []
			for m in range(len(operands)): #random_sample(iter(range(len(operands))), len(operands), min(len(operands), 64)):
				for n in range(m): #random_sample(iter(range(m)), m, min(m, 64)):
					s = operands[m]
					t = operands[n]
					
					f, c = (s + t).flatten().__optimize_refactor()
					if f.is_identically_one(): continue
					
					pairs.append((f, c, m, n))
			
			if not pairs:
				return current
			
			addends = []
			taken = set()
			pairs.sort(key=lambda _t: -_t[0].circuit_size())
			for f, c, m, n in pairs:
				if (m not in taken) and (n not in taken):
					addends.append(f * c)
					taken.add(m)
					taken.add(n)
			del pairs
			
			r = self.algebra.sum([operands[_i] for _i in range(len(operands)) if _i not in taken]).flatten().__optimize_common_factors(depth+1)
			addends.append(r)
			
			equiv = self.algebra.sum(addends).flatten()
			if equiv.circuit_size() < current.circuit_size():
				current = equiv
				iteration += 1
				continue
			
			return equiv
	
	def optimized(self):
		if self.is_optimized or self.circuit_size() <= 1:
			return self
		elif hasattr(self, 'optimized_cache'):
			assert self.optimized_cache.is_optimized
			return self.optimized_cache
		
		#print("optimize", self.circuit_size(), hex(hash(str(self))))
		
		#smallest_circuit = flat.__optimize_smallest(flat.__optimize_additive_form().__optimize_equivalent_forms())
		smallest_circuit = self.flatten().__optimize_additive_form().__optimize_common_factors()
		#smallest_circuit = self.flatten().__optimize_additive_form()
		
		smallest_circuit.is_optimized = True
		if self.canonical_caching and hasattr(self, 'canonical_cache'): smallest_circuit.canonical_cache = self.canonical_cache
		if self.optimized_caching: self.optimized_cache = smallest_circuit
		#print(" optimized", self.circuit_size(), smallest_circuit.circuit_size(), (self.circuit_size() / smallest_circuit.circuit_size() if smallest_circuit.circuit_size() else "inf"), self.circuit_depth(), smallest_circuit.circuit_depth())
		return smallest_circuit
	
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
		return self.__class__.__qualname__ + '(' + str(self.operator) + ', ' + repr(self.operands) + ')'
	
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
		try:
			return not self.is_zero()
		except ValueError:
			return True
		
		#c = self.canonical()
		#if c.operator == self.symbol.const:
		#	try:
		#		return bool(c.operands[0])
		#	except IndexError:
		#		return False
		#else:
		#	return True
	
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
		
		if len(variables) * self.algebra.base_ring.size > self.variables_threshold:
			if not hasattr(other, 'operator'):
				other_canonical = self.const(other).canonical()
			else:
				other_canonical = other.canonical()
			
			self_canonical = self.canonical()
			
			try:
				return self_canonical.operator == other_canonical.operator and self_canonical.operands == other_canonical.operands		
			except AttributeError:
				return NotImplemented
		elif other_is_const:
			for valuation in valuations(*variables):
				if self(**valuation).evaluate() != other:
					return False
			else:
				return True
		else:
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
			return self.algebra.sum(self.operands + other.operands)
		else:
			return self.algebra.sum([self, other])
	
	def __radd__(self, other):
		if other.algebra != self.algebra:
			other = self.algebra.const(other)
		if self.operator == other.operator == self.symbol.add:
			return self.algebra.sum(other.operands + self.operands)
		else:
			return self.algebra.sum([other, self])
	
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
			return self.algebra.product(self.operands + other.operands)
		else:
			return self.algebra.product([self, other])
	
	def __rmul__(self, other):
		try:
			if other.algebra != self.algebra:
				other = self.algebra.const(other)
		except (AttributeError, ValueError):
			return NotImplemented
		
		if self.operator == other.operator == self.symbol.mul:
			return self.algebra.product(other.operands + self.operands)
		else:
			return self.algebra.product([other, self])
	
	@staticmethod
	def __monomial_division(dividend, divisor):
		if not dividend.is_multiplicative_normal_form():
			raise ValueError("Dividend must be in multiplicative normal form.")
		if not divisor.is_canonical_monomial():
			#print(divisor)
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
		
		#print([str(_e) for _e in dividend_vars.elements()], [str(_e) for _e in dividend_factors], [str(_e) for _e in divisor_vars])
		
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
			#print(monomial)
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
	
	def __rdivmod__(self, other):
		return divmod(self.const(other), self)
	
	def __truediv__(self, other):
		quotient, remainder = divmod(self, other)
		if remainder:
			#print(self, '/', other, '=', quotient, '+', remainder)
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
		
		if self.is_canonical_polynomial():
			c = self
		else:
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
			try:
				result = evaluate(self.operands[0])
			except IndexError:
				return self.algebra.base_ring.zero()
			for operand in parallel_map(evaluate, self.operands[1:]):
				if operand.is_jit() or not operand.is_zero():
					result += operand
			return result
		elif self.operator == self.symbol.mul:
			if any((not hasattr(_op, 'operator') or _op.operator == self.symbol.const) and (not _op.is_jit() and _op.is_zero()) for _op in self.operands):
				return self.algebra.base_ring.zero()
			try:
				result = evaluate(self.operands[0])
			except IndexError:
				return self.algebra.base_ring.one()
			for operand in parallel_map(evaluate, self.operands[1:]):
				if operand.is_jit():
					result *= operand
				elif operand.is_zero():
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
	
	def is_jit(self):
		return (self.operator == self.symbol.const) and len(self.operands) >= 1 and self.operands[0].is_jit()
	
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
		
		#print(bits)
		
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
		
		assert (x * x + y) // (x * x) == x
		assert (x * x + y) // (y + x * x) == x + y
		
		assert (x * y)(x=yes, y=no) == no
		assert (x * y)(x=yes, y=yes) == yes
		assert (x + y)(x=yes, y=no) == yes
		assert (x * y + x)(x=z) == (z * y + z)
		assert (x * y + x)(x=y) == no if x**2 + x == no else True
		assert (x * y)(x=z, y=z) == z if x**2 == x else True
		
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
			assert a // yes == a
			
			assert a**1 == a
			
			try:
				assert a**0 == yes
			except ZeroDivisionError:
				assert not a
			except ArithmeticError:
				assert yes % a
			
			# FIXME: fails
			try:
				assert (a**-1 == yes // a) or (yes % a)
			except ZeroDivisionError:
				assert not a
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
			assert (-a) * (-b) == a * b
			
			try:
				q, r = divmod(a, b)
				assert q * b + r == a
				
				assert q == a // b
				assert r == a % b
			except ZeroDivisionError:
				assert not b
		
		for a, b, c in product(random_polynomials(4), random_polynomials(4), random_polynomials(4)):
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
	
	def test_optimization(algebra):
		v = [algebra.var('v_' + str(_n)) for _n in range(16)]
		
		for i in range(5):
			p = algebra.random(variables=v, order=10).flatten()
			po = p.optimized()
			print(" ", p.circuit_size(), po.circuit_size(), p.circuit_depth(), po.circuit_depth(), po)
			assert p.circuit_size() >= po.circuit_size()
			with AllowCanonical():
				assert po == p
	
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
			test_optimization(ring_polynomial)
		
		ring = BooleanRing.get_algebra()
		if verbose: print()
		if verbose: print("test Polynomial(base_ring=BooleanRing())")
		ring_polynomial = Polynomial.get_algebra(base_ring=ring)
		if verbose: print(" ring test")
		test_ring(ring_polynomial)
		if verbose: print(" polynomial test")
		test_polynomial(ring_polynomial)
		if verbose: print(" optimization test")
		test_optimization(ring_polynomial)
		
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
			test_optimization(ring_polynomial)
		
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
			test_optimization(ring_polynomial)
		
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
		test_optimization(ring_polynomial)
	
	__all__ = __all__ + ('test_polynomial', 'test_optimization', 'polynomial_test_suite')


if __debug__ and __name__ == '__main__':
	#polynomial_test_suite(verbose=True)
	#test_optimization(Polynomial.get_algebra(base_ring=BooleanRing.get_algebra()))
	
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







