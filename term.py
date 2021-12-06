#!/usr/bin/python3
#-*- coding:utf8 -*-

"""
Optimized transformation algorithms on generic terms.
"""


__all__ = 'Identical', 'Term', 'cached'


from collections import Counter, defaultdict
from itertools import product


class Identical:
	"When a term is wrapped in this class, it can be used as dictionary key. Comparison is identity-based."
	
	def __init__(self, term):
		self.term = term
		self.str_cache = None
	
	def __eq__(self, other):
		if self.term is other.term:
			return True
		
		if hash(self) != hash(other):
			return False
		
		try:
			if self.term.is_const():
				if other.term.is_const():
					return self.term.const_value() == other.term.const_value()
				else:
					return False
		except AttributeError:
			return NotImplemented
		
		if self.term.is_var():
			if other.term.is_var():
				return self.term.var_name() == other.term.var_name()
			else:
				return False
		
		try:
			if self.term.p_operator != other.term.p_operator:
				return False
		except AttributeError:
			if not ((self.term.is_add() and other.term.is_add()) or (self.term.is_sub() and other.term.is_sub()) or (self.term.is_mul() and other.term.is_mul()) or (self.term.is_neg() and other.term.is_neg())):
				return False

		if len(self.term.subterms()) != len(other.term.subterms()):
			return False
		
		result = all((self.__class__(_a) == self.__class__(_b)) for (_a, _b) in zip(self.term.subterms(), other.term.subterms()))
				
		return result
	
	def shallow_hash(self, depth):
		if self.term.is_const():
			return hash(('const', self.term.const_value()))
		elif self.term.is_var():
			return hash(('var', self.term.var_name()))
		
		if depth <= 0:
			return hash((self.term.is_add(), self.term.is_sub(), self.term.is_mul(), self.term.is_neg(), len(self.term.subterms())))
		else:
			return hash((self.term.is_add(), self.term.is_sub(), self.term.is_mul(), self.term.is_neg()) + tuple(Identical(_subterm).shallow_hash(depth - _n - 1) for (_n, _subterm) in enumerate(self.term.subterms())))
	
	def __hash__(self):
		try:
			if self.term.is_const():
				return hash(self.term.const_value())
			elif self.term.is_var():
				return hash(self.term.var_name())
			else:
				return self.term.identical_hash
		except AttributeError:
			return 0
	
	def __str__(self):
		if self.str_cache != None:
			return self.str_cache
		self.str_cache = str(self.term)
		return self.str_cache


class Constant:
	def __init__(self, value):
		self.value = value
	
	@classmethod
	def zero(cls):
		return cls(0)
	
	@classmethod
	def one(cls):
		return cls(1)
	
	def is_zero(self):
		return self.value == 0
	
	def is_one(self):
		return self.value == 1
	
	@classmethod
	def sum(cls, addends):
		return cls(sum(_addend.value for _addend in addends) % 2)
	
	@classmethod
	def product(cls, factors):
		return cls(all(_factor.value for _factor in factors))
	
	def __add__(self, other):
		return self.__class__(self.value ^ other.value)
	
	def __mul__(self, other):
		return self.__class__(self.value & other.value)
	
	def __sub__(self, other):
		return self + -other
	
	def __neg__(self):
		return self
	
	@classmethod
	def domain(cls):
		yield cls.zero()
		yield cls.one()
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + repr(self.value) + ')'
	
	def __str__(self):
		return str(self.value)
	
	def sort_ordering(self):
		return str(self)
	
	def __eq__(self, other):
		try:
			return self.value == other.value
		except AttributeError:
			return NotImplemented
	
	def __hash__(self):
		return hash((94387, self.value))


def sorted_and_unique(old_gen):
	def new_gen(self, *args, **kwargs):
		monomials = defaultdict(lambda: self.algebra.base_ring.zero())
		one = self.algebra.base_ring.one()
		for monomial in old_gen(self, *args, **kwargs):
			monomial = monomial.traverse_before(self.__class__.flatten).evaluate_repetitions().evaluate_constants().order().traverse_before(self.__class__.flatten)
			
			if monomial.is_const():
				monomial_f = self.algebra.one()
				monomial_c = monomial.const_value()
			elif monomial.is_var():
				monomial_f = monomial
				monomial_c = one
			elif monomial.is_mul():
				monomial_f = self.algebra.product(_f for _f in monomial.subterms() if _f.is_var()).fixed_point(self.__class__.flatten).order()
				monomial_c = self.algebra.product(_f for _f in monomial.subterms() if _f.is_const()).fixed_point(self.__class__.flatten).evaluate_constants().const_value()
			else:
				raise RuntimeError
			
			assert all((_op.is_const() or _op.is_var()) for _op in monomial.subterms()) if monomial.is_mul() else True, str(monomial)
			#print(monomial, monomial_f, monomial_c)
			monomials[Identical(monomial_f)] += monomial_c
		
		for monomial_id in sorted(monomials.keys(), key=lambda m_id: m_id.term.sort_ordering()):
			monomial = monomial_id.term
			monomial = (monomial * self.algebra.const(monomials[monomial_id])).evaluate_constants().flatten().order()
			if not (monomial.is_const() and monomial.is_zero()):
				yield monomial
	
	return new_gen


'''
def cached(old_method):
	name = old_method.__qualname__
	
	def new_method(self):
		try:
			return self.__class__.cache[name][Identical(self)]
		except KeyError:
			result = old_method(self)
			self.__class__.cache[name][Identical(self)] = result
			return result
	
	new_method.__qualname__ = name
	return new_method
'''


def cached(old_method):
	name = old_method.__name__
	
	def new_method(self):
		try:
			return getattr(self, 'cached_' + name)
		except AttributeError:
			result = old_method(self)
			setattr(self, 'cached_' + name, result)
			return result
	
	new_method.__name__ = name
	return new_method


def cached_broad(old_method):
	name = old_method.__name__
	
	def new_method(self):
		cache =  getattr(self.__class__, 'cached_' + name)
		i_self = Identical(self)
		try:
			return cache[i_self]
		except KeyError:
			result = old_method(self)
			cache[i_self] = result
			return result
	
	new_method.__name__ = name
	return new_method


class Term:
	cached_is_zero = {}
	cached_is_one = {}
	cached_has_nonreduced_constants = {}
	
	def __init__(self, operator, operands):
		#if not isinstance(operator, str):
		#	raise ValueError("Operator must be a string.")
		self.operator = operator
		self.operands = operands
		self.calculate_identical_hash()
	
	def calculate_identical_hash(self):
		if not self.is_const() and not self.is_var() and not self.is_jit():
			try:
				operator = self.operator
			except AttributeError:
				operator = self.p_operator
			self.identical_hash = hash((operator,) + tuple(hash(Identical(_operand)) for _operand in self.subterms()))
	
	@classmethod
	def const(cls, value):
		return cls('const', value)
	
	@classmethod
	def var(cls, name):
		return cls('var', name)
	
	@classmethod
	def zero(cls):
		return cls.const(Constant(0))
	
	@classmethod
	def one(cls):
		return cls.const(Constant(1))
	
	@classmethod
	def sum(cls, addends):
		return cls('add', list(addends))
	
	@classmethod
	def product(cls, factors):
		return cls('mul', list(factors))
	
	def __add__(self, other):
		return self.__class__('add', [self, other])
	
	def __mul__(self, other):
		return self.__class__('mul', [self, other])
	
	def __sub__(self, other):
		return self.__class__('sub', [self, other])
	
	def __neg__(self):
		return self.__class__('neg', [self])
	
	def __pow__(self, exp):
		"Exponentiation in Boolean ring. `x**2 == x`"
		
		if exp < 0:
			raise ArithmeticError("Negative exponents not supported.")
		
		if exp == 0 and self.is_zero():
			raise ArithmeticError("Cannot raise 0 to 0 power.")
		
		if exp == 0:
			return self.algebra.one()
		
		if exp >= 1:
			return self
	
	def is_jit(self):
		return False
	
	def is_var(self):
		return self.operator == 'var'
	
	def is_const(self):
		return self.operator == 'const'
	
	def is_add(self):
		return self.operator == 'add'
	
	def is_mul(self):
		return self.operator == 'mul'
	
	def is_sub(self):
		return self.operator == 'sub'
	
	def is_neg(self):
		return self.operator == 'neg'
	
	def subterms(self):
		"Return the subterms to iterate over."
		if not self.is_const() and not self.is_var():
			return self.operands
		else:
			raise ValueError("Constants and variables do not have subterms.")
	
	def const_value(self):
		"Return the value of the constant (type: `self.base_ring`)."
		if self.is_const():
			return self.operands
		else:
			raise ValueError("Only constants have a value.")
	
	def var_name(self):
		"Return the name of the variable (type: `str`)."
		if self.is_var():
			return self.operands
		else:
			raise ValueError("Only variables have a name.")
	
	@property
	def algebra(self):
		return self
	
	@property
	def base_ring(self):
		return Constant
	
	def variables(self):
		"Yield all variables in the polynomial."
		
		if self.is_const():
			pass
		elif self.is_var():
			yield self
		else:
			for subterm in self.subterms():
				yield from subterm.variables()
	
	@cached
	def variables_set(self):
		return frozenset(_v.term for _v in frozenset(Identical(_u) for _u in self.variables()))
	
	def variables_count(self):
		return Counter(_u.var_name() for _u in self.variables())
	
	def __call__(self, **substitution):
		"Substitute the variables in the polynomial for the provided terms."
		
		if self.is_const():
			return self
		elif self.is_var():
			try:
				return self.algebra(substitution[str(self)])
			except KeyError:
				return self
		elif not frozenset(str(_v) for _v in self.variables()) & frozenset(substitution.keys()):
			return self
		elif self.is_add():
			return self.algebra.sum(_subterm(**substitution) for _subterm in self.subterms())
		elif self.is_mul():
			return self.algebra.product(_subterm(**substitution) for _subterm in self.subterms())
		elif self.is_sub():
			return self.subterms()[0](**substitution) - self.subterms()[1](**substitution)
		elif self.is_neg():
			return -self.subterms()[0](**substitution)
		else:
			raise RuntimeError
	
	def evaluate(self, **substitution):
		"Substitute all variables with constants and evaluate the resulting constant."
		
		if self.is_const():
			return self.const_value()
		elif self.is_var():
			return substitution[str(self)]
		#elif not frozenset(str(_v) for _v in self.variables()) & frozenset(substitution.keys()):
		#	return self
		elif self.is_add():
			return self.algebra.base_ring.sum([_subterm.evaluate(**substitution) for _subterm in self.subterms()])
		elif self.is_mul():
			return self.algebra.base_ring.product([_subterm.evaluate(**substitution) for _subterm in self.subterms()])
		elif self.is_sub():
			return self.subterms()[0].evaluate(**substitution) - self.subterms()[1].evaluate(**substitution)
		elif self.is_neg():
			return -self.subterms()[0].evaluate(**substitution)
		else:
			raise RuntimeError
	
	@sorted_and_unique
	def monomials(self):
		if self.is_const():
			if not self.is_zero():
				yield self
		
		elif self.is_var():
			yield self
		
		elif self.is_add():
			for subterm in self.subterms():
				yield from subterm.monomials()
		
		elif self.is_mul():
			#print()
			for monomial_tuple in product(*[_subterm.monomials() for _subterm in self.subterms()]):
				#print([str(_x) for _x in monomial_tuple], self.algebra.product(monomial_tuple))
				yield self.algebra.product(monomial_tuple)
		
		elif self.is_sub():
			a, b = self.subterms()
			yield from (a + (-b)).monomials()
		
		elif self.is_neg():
			for monomial in self.subterms()[0].monomials():
				yield self.algebra.const(-self.algebra.base_ring.one()) * monomial
		
		else:
			raise RuntimeError
	
	@cached
	def circuit_size(self):
		if self.is_const():
			return 0
		elif self.is_var():
			return 1
		elif self.is_add() or self.is_mul():
			return len(self.subterms()) + sum(_subterm.circuit_size() for _subterm in self.subterms()) - 1
		elif self.is_sub():
			return 1 + sum(_subterm.circuit_size() for _subterm in self.subterms())
		elif self.is_neg():
			return 1 + self.subterms()[0].circuit_size()
		else:
			raise RuntimeError
	
	def circuit_depth(self):
		if self.is_const() or self.is_var():
			return 0
		elif self.is_add() or self.is_mul() or self.is_sub():
			return 1 + max(_operand.circuit_depth() for _operand in self.subterms())
		elif self.is_neg():
			return 1 + self.subterms()[0].circuit_depth()
		else:
			raise RuntimeError
	
	def circuit_width(self):
		if self.is_const() or self.is_var():
			return 1
		elif self.is_add() or self.is_mul() or self.is_sub():
			return sum(_operand.circuit_width() for _operand in self.subterms())
		elif self.is_neg():
			return self.symbol.operands[0].circuit_width()
		else:
			raise RuntimeError
	
	@cached_broad
	def is_zero(self):
		"Checks if the polynomial is identically 0. This is an expensive check, exponential in worst case."
		
		#print("    is_zero", self.circuit_size(), len(self.variables_set()), hex(abs(hash(Identical(self)))))
		
		current = self.additive_form().flatten()
		
		if current.is_const():
			return current.const_value().is_zero()
		
		elif current.is_var():
			return False
		
		elif not frozenset(Identical(_var) for _var in current.variables()):
			return current.evaluate().is_zero()
		
		for n in range(16): # <- optimization parameter
			if not current.evaluate(**{str(_v):self.algebra.base_ring.random() for _v in self.variables()}).is_zero():
				return False
		
		if current.is_add():
			if len(self.subterms()) == 0:
				return True
			elif len(self.subterms()) == 1:
				return self.subterms()[0].is_zero()
			
			current_variables = Counter(Identical(_var) for _var in current.variables())
			var_count = len(frozenset(current_variables.keys()))
			mc_var_id, _ = current_variables.most_common()[0]
			mc_var = mc_var_id.term
			
			if var_count > 4: # optimization parameter
				longest = self.algebra.zero()
				longest_pos = len(current.subterms())
				for n, subterm in enumerate(current.subterms()):
					if len(frozenset(Identical(_var) for _var in subterm.variables())) > len(frozenset(Identical(_var) for _var in longest.variables())):
						longest = subterm
						longest_pos = n
				
				group_1 = [longest]
				group_2 = [_subterm for (_n, _subterm) in enumerate(current.subterms()) if _n != longest_pos]
				while group_2:
					for n, subterm_2 in enumerate(group_2[:]):
						if any(frozenset(Identical(_var) for _var in subterm_1.variables()) & frozenset(Identical(_var) for _var in subterm_2.variables()) for subterm_1 in group_1):
							group_1.append(subterm_2)
							del group_2[n]
							break
					else:
						break
				
				if group_2:
					a = self.algebra.sum(group_1)
					b = self.algebra.sum(group_2)
					assert not frozenset(Identical(_var) for _var in a.variables()) & frozenset(Identical(_var) for _var in b.variables())
					if (b.is_zero() and a.is_zero()) or ((-b).is_one() and a.is_one()) or (b.is_one() and (-a).is_one()):
						return True
					# TODO: if `a` or `b` is not constant, return `False`
			
			for d in self.algebra.base_ring.domain():
				if not current(**{str(mc_var):self.algebra.const(d)}).is_zero():
					return False
			
			return True
		
		elif current.is_mul():
			if len(self.subterms()) == 0:
				return False
			elif len(self.subterms()) == 1:
				return self.subterms()[0].is_zero()
			
			for subterm in sorted(current.subterms(), key=self.__class__.circuit_size):
				if subterm.is_zero():
					return True
			else:
				return False
		
		else:
			raise RuntimeError
	
	@cached_broad
	def is_one(self):
		"Checks if the polynomial is identically 1. This is an expensive check, exponential in worst case."
		
		#print("    is_one", self.circuit_size(), len(self.variables_set()), hex(abs(hash(Identical(self)))))
		
		current = self.additive_form().flatten()
		
		if current.is_const():
			return current.const_value().is_one()
		
		elif current.is_var():
			return False
		
		elif not frozenset(Identical(_var) for _var in current.variables()):
			return current.evaluate().is_one()
		
		for n in range(16): # <- optimization parameter
			if not current.evaluate(**{str(_v):self.algebra.base_ring.random() for _v in self.variables()}).is_one():
				return False
		
		if current.is_add():
			if len(current.subterms()) == 0:
				return False
			elif len(current.subterms()) == 1:
				return current.subterms()[0].is_one()
			
			current_variables = Counter(Identical(_var) for _var in current.variables())
			var_count = len(frozenset(current_variables.keys()))
			mc_var_id, _ = current_variables.most_common()[0]
			mc_var = mc_var_id.term
			
			if var_count > 4: # optimization parameter
				longest = self.algebra.zero()
				longest_pos = len(current.subterms())
				for n, subterm in enumerate(current.subterms()):
					if len(frozenset(Identical(_var) for _var in subterm.variables())) > len(frozenset(Identical(_var) for _var in longest.variables())):
						longest = subterm
						longest_pos = n
				
				group_1 = [longest]
				group_2 = [_subterm for (_n, _subterm) in enumerate(current.subterms()) if _n != longest_pos]
				while group_2:
					for n, subterm_2 in enumerate(group_2[:]):
						if any(frozenset(Identical(_var) for _var in subterm_1.variables()) & frozenset(Identical(_var) for _var in subterm_2.variables()) for subterm_1 in group_1):
							group_1.append(subterm_2)
							del group_2[n]
							break
					else:
						break
				
				if group_2:
					a = self.algebra.sum(group_1)
					b = self.algebra.sum(group_2)
					assert not frozenset(Identical(_var) for _var in a.variables()) & frozenset(Identical(_var) for _var in b.variables())
					if (b.is_one() and a.is_zero()) or (b.is_zero() and a.is_one()):
						return True
					# TODO: if `a` or `b` is not constant, return `False`
			
			for d in self.algebra.base_ring.domain():
				if not current(**{str(mc_var):self.algebra.const(d)}).is_one():
					return False
			
			return True
		
		elif current.is_mul():
			if len(self.subterms()) == 0:
				return True
			elif len(self.subterms()) == 1:
				return self.subterms()[0].is_one()
			
			for subterm in sorted(current.subterms(), key=self.__class__.circuit_size):
				if subterm.is_zero():
					return False
				elif not subterm.is_one():
					break
			
			current_af = current.additive_form()
			if Identical(current_af) != Identical(current):
				return current_af.is_one()
			else:
				return False
		
		else:
			raise RuntimeError
	
	def fixed_point(self, transform):
		term = self
		iden_term = Identical(term)
		#size = term.circuit_size()
		
		term_history = []
		#size_history = []
		
		#while all(size < prev_size for prev_size in size_history) and all(iden_term != prev_term for prev_term in term_history):
		while all(iden_term != prev_term for prev_term in term_history):
			term_history.append(iden_term)
			if len(term_history) > 6:
				term_history = term_history[-6:]
			
			#size_history.append(term.circuit_size())
			#if len(size_history) > 5:
			#	size_history = size_history[-5:]
			
			term = transform(term)
			iden_term = Identical(term)
			#size = term.circuit_size()
		
		return term
	
	def shrinking(self, transform):
		term = self
		new_size = term.circuit_size()
		old_size = new_size + 1
		while new_size < old_size:
			term = transform(term)
			old_size = new_size
			new_size = term.circuit_size()
		return term
	
	def traverse_before(self, transform):
		"Apply the transformation on all subterms (recursively) and then on the resulting term."
		
		if self.is_add():
			addends = [_subterm.traverse_before(transform) for _subterm in self.subterms()]
			if all(_a is _b for (_a, _b) in zip(addends, self.subterms())): # optimization: don't reconstruct the tree if all subtrees are the same as original
				candidate = self
			else:
				candidate = self.algebra.sum(addends)
		elif self.is_mul():
			factors = [_subterm.traverse_before(transform) for _subterm in self.subterms()]
			if all(_a is _b for (_a, _b) in zip(factors, self.subterms())): # optimization: don't reconstruct the tree if all subtrees are the same as original
				candidate = self
			else:
				candidate = self.algebra.product(factors)
		elif self.is_sub():
			left, right = [_subterm.traverse_before(transform) for _subterm in self.subterms()]
			candidate = left - right
		elif self.is_neg():
			candidate = -self.subterms()[0].traverse_before(transform)
		else:
			candidate = self
		
		return transform(candidate)
	
	def traverse_before_filtered(self, transform, filter_, recurse):
		"Apply the transformation on all subterms (recursively) and then on the resulting term."
		
		if not recurse(self):
			candidate = self
		elif self.is_add():
			addends = [_subterm.traverse_before_filtered(transform, filter_, recurse) for _subterm in self.subterms()]
			if all(_a is _b for (_a, _b) in zip(addends, self.subterms())): # optimization: don't reconstruct the tree if all subtrees are the same as original
				candidate = self
			else:
				candidate = self.algebra.sum(addends)
		elif self.is_mul():
			factors = [_subterm.traverse_before_filtered(transform, filter_, recurse) for _subterm in self.subterms()]
			if all(_a is _b for (_a, _b) in zip(factors, self.subterms())): # optimization: don't reconstruct the tree if all subtrees are the same as original
				candidate = self
			else:
				candidate = self.algebra.product(factors)
		elif self.is_sub():
			left, right = [_subterm.traverse_before_filtered(transform, filter_, recurse) for _subterm in self.subterms()]
			candidate = left - right
		elif self.is_neg():
			candidate = -self.subterms()[0].traverse_before_filtered(transform, filter_, recurse)
		else:
			candidate = self
		
		if filter_(candidate):
			return transform(candidate)
		else:
			return candidate
	
	'''
	def traverse_before_filtered(self, transform, filter_):
		"Apply the transformation on all subterms (recursively) and then on the resulting term."
		
		if self.is_add():
			addends = [_subterm.traverse_before(transform) if filter_(_subterm) else _subterm for _subterm in self.subterms()]
			if all(_a is _b for (_a, _b) in zip(addends, self.subterms())): # optimization: don't reconstruct the tree if all subtrees are the same as original
				candidate = self
			else:
				candidate = self.algebra.sum(addends)
		elif self.is_mul():
			factors = [_subterm.traverse_before(transform) if filter_(_subterm) else _subterm for _subterm in self.subterms()]
			if all(_a is _b for (_a, _b) in zip(factors, self.subterms())): # optimization: don't reconstruct the tree if all subtrees are the same as original
				candidate = self
			else:
				candidate = self.algebra.product(factors)
		elif self.is_sub():
			left, right = [_subterm.traverse_before(transform) if filter_(_subterm) else _subterm for _subterm in self.subterms()]
			if left is self.subterms()[0] and right is self.subterms()[1]:
				candidate = self
			else:
				candidate = left - right
		elif self.is_neg():
			if filter_(self.subterms()[0]):
				transformed = self.subterms()[0].traverse_before(transform)
				if transformed is self.subterms()[0]:
					candidate = self
				else:
					candidate = -transformed
			else:
				candidate = self
		else:
			candidate = self
		
		if filter_(candidate):
			return transform(candidate)
		else:
			return candidate
	'''
	
	def traverse_after(self, transform):
		"Apply the transformation on the term and then on all its subterms (recursively)."
		
		candidate = transform(self)
		
		if candidate.is_add():
			return self.algebra.sum(_subterm.traverse_after(transform) for _subterm in candidate.subterms())
		elif candidate.is_mul():
			return self.algebra.product(_subterm.traverse_after(transform) for _subterm in candidate.subterms())
		elif candidate.is_sub():
			left, right = [_subterm.traverse_after(transform) for _subterm in candidate.subterms()]
			return left - right
		elif candidate.is_neg():
			return -(candidate.subterms()[0].traverse_after(transform))
		else:
			return candidate
	
	def traverse_after_filtered(self, transform, filter_, recurse):
		"Apply the transformation on the term and then on all its subterms (recursively)."
		
		if filter_(self):
			candidate = transform(self)
		else:
			candidate = self
		
		if not recurse(self):
			return candidate
		elif candidate.is_add():
			return self.algebra.sum(_subterm.traverse_after_filtered(transform, filter_, recurse) for _subterm in candidate.subterms())
		elif candidate.is_mul():
			return self.algebra.product(_subterm.traverse_after_filtered(transform, filter_, recurse) for _subterm in candidate.subterms())
		elif candidate.is_sub():
			left, right = [_subterm.traverse_after_filtered(transform, filter_, recurse) for _subterm in candidate.subterms()]
			return left - right
		elif candidate.is_neg():
			return -(candidate.subterms()[0].traverse_after_filtered(transform, filter_, recurse))
		else:
			return candidate
	
	'''
	def traverse_after_filtered(self, transform, filter_):
		"Apply the transformation on the term and then on all its subterms (recursively)."
		
		candidate = transform(self)
		
		if candidate.is_add():
			return self.algebra.sum(_subterm.traverse_after(transform) if filter_(_subterm) else _subterm for _subterm in candidate.subterms())
		elif candidate.is_mul():
			return self.algebra.product(_subterm.traverse_after(transform) if filter_(_subterm) else _subterm for _subterm in candidate.subterms())
		elif candidate.is_sub():
			left, right = [_subterm.traverse_after(transform) if filter_(_subterm) else _subterm for _subterm in candidate.subterms()]
			return left - right
		elif candidate.is_neg():
			if filter_(self.subterms()[0]):
				transformed = self.subterms()[0].traverse_after(transform)
				if transformed is self.subterms()[0]:
					candidate = self
				else:
					candidate = -transformed
			else:
				candidate = self
		else:
			return candidate
	'''
	
	@cached_broad
	def has_nonreduced_constants(self):
		if self.is_const() or self.is_var():
			return False
		
		elif self.is_add():
			cc = Counter(_subterm.const_value() for _subterm in self.subterms() if _subterm.is_const())
			if cc[self.algebra.base_ring.zero()] != 0 or len(cc) > 1:
				return True
		
		elif self.is_mul():
			cc = Counter(_subterm.const_value() for _subterm in self.subterms() if _subterm.is_const())
			if cc[self.algebra.base_ring.zero()] != 0 or cc[self.algebra.base_ring.one()] != 0 or len(cc) > 1:
				return True
		
		elif self.is_neg() and self.subterms()[0].is_const():
			return True
		
		elif self.is_sub():
			if all(_operand.is_const() for _operand in self.subterms()):
				return True
			elif self.subterms()[1].is_const() and self.subterms()[1].is_zero():
				return True
			elif self.subterms()[0].is_const() and self.subterms()[0].is_zero():
				return True
		
		return any(_subterm.has_nonreduced_constants() for _subterm in self.subterms())
	
	def evaluate_constants(self):
		"Simplifies the polynomial by removing 1s and 0s."
		
		if self.is_neg() and self.subterms()[0].is_const():
			return self.algebra.const(-self.subterms()[0].const_value())
		
		elif self.is_sub():
			if all(_operand.is_const() for _operand in self.subterms()):
				return self.algebra.const(self.subterms()[0].const_value() - self.subterms()[1].const_value())
			elif self.subterms()[1].is_const() and self.subterms()[1].is_zero():
				return self.subterms()[0]
			elif self.subterms()[0].is_const() and self.subterms()[0].is_zero():
				return -self.subterms()[1]
		
		elif self.is_add():
			allconst = [_subterm.const_value() for _subterm in self.subterms() if _subterm.is_const()]
			cc = Counter(allconst)
			##print("    add", cc)
			if cc[self.algebra.base_ring.zero()] == 0 and len(allconst) <= 1:
				return self
			
			constant = self.algebra.base_ring.zero()
			operands = []
			for subterm in self.subterms():
				if subterm.is_const():
					constant += subterm.const_value()
				else:
					operands.append(subterm)
			#return self.algebra.sum(operands + [self.algebra.const(constant)])
			
			if not operands and constant.is_zero():
				return self.algebra.zero()
			elif operands and constant.is_zero():
				if len(operands) == 1:
					return operands[0]
				else:
					return self.algebra.sum(operands)
			elif not operands and not constant.is_zero():
				return self.algebra.const(constant)
			elif operands and not constant.is_zero():
				return self.algebra.sum(operands + [self.algebra.const(constant)])
		
		elif self.is_mul():
			allconst = [_subterm.const_value() for _subterm in self.subterms() if _subterm.is_const()]
			cc = Counter(allconst)
			##print("    mul", cc)
			if cc[self.algebra.base_ring.zero()] == 0 and cc[self.algebra.base_ring.one()] == 0 and len(allconst) <= 1:
				return self
			
			constant = self.algebra.base_ring.one()
			operands = []
			for subterm in self.subterms():
				if subterm.is_const():
					constant *= subterm.const_value()
				else:
					operands.append(subterm)
			#return self.algebra.product(operands + [self.algebra.const(constant)])
			
			if constant.is_zero():
				return self.algebra.zero()
			elif not operands and constant.is_one():
				return self.algebra.one()
			elif operands and constant.is_one():
				if len(operands) == 1:
					return operands[0]
				else:
					return self.algebra.product(operands)
			elif not operands and not constant.is_one():
				return self.algebra.const(constant)
			elif operands and not constant.is_one():
				return self.algebra.product(operands + [self.algebra.const(constant)])
		
		return self
	
	def evaluate_constant_term(self):
		"Simplifies the polynomial by replacing term identically equal to 1 or 0 by a constant."
		
		if self.is_const() or self.is_var():
			return self
		
		random_result = self.evaluate(**{str(_v):self.algebra.base_ring.random() for _v in self.variables()})
		
		if random_result.is_zero() and self.is_zero():
			return self.algebra.zero()
		elif random_result.is_one() and self.is_one():
			return self.algebra.one()
		else:
			return self
	
	def evaluate_repetitions(self):
		if self.is_sub():
			a, b = self.subterms()
			if Identical(a) == Identical(b):
				return self.algebra.zero()
			else:
				return self
		
		elif self.is_add():
			operands = Counter()
			#print("     evaluate repetitions: ", len(self.subterms()))
			for subterm in self.subterms():
				operands[Identical(subterm)] += 1
			#print("      evaluate repetitions most common:", [_v for (_k, _v) in operands.most_common()[:5]], all(_v == 1 for _v in operands.values()))
			
			if all(_v == 1 for _v in operands.values()):
				return self
			
			#operands = defaultdict(lambda: self.algebra.base_ring.zero())
			#for subterm in self.subterms():
			#	operands[Identical(subterm)] += self.algebra.base_ring.one()
			
			one = self.algebra.base_ring.one()
			addends = []
			for operand, reps in operands.items():
				factor = self.algebra.base_ring.zero()
				for n in range(reps):
					factor += one
				
				if factor.is_zero():
					pass
				elif factor.is_one():
					addends.append(operand.term)
				else:
					addends.append(self.algebra.const(factor) * operand.term)
			
			if len(addends) == 0:
				return self.algebra.zero()
			elif len(addends) == 1:
				return addends[0]
			else:
				return self.algebra.sum(addends)
		
		elif self.is_mul():
			operands = Counter()
			#print("     evaluate repetitions: ", len(self.subterms()))
			for subterm in self.subterms():
				operands[Identical(subterm)] += 1
			#print("      evaluate repetitions most common:", [_v for (_k, _v) in operands.most_common()[:5]], all(_v == 1 for _v in operands.values()))
			
			if all(_v == 1 for _v in operands.values()):
				return self
			
			factors = []
			for operand, exponent in operands.items():
				if exponent == 0:
					factors.append(self.algebra.one())
				elif exponent == 1:
					factors.append(operand.term)
				else:
					factors.append(operand.term ** exponent)
			
			if len(factors) == 0:
				return self.algebra.one()
			elif len(factors) == 1:
				return factors[0]
			else:
				return self.algebra.product(factors)
		
		else:
			return self
	
	def flatten(self):
		"Applies the law of conjunctivity on addition and multiplication to flatten the hierarchy. Also called 'omitting brackets'."
		
		if self.is_add():
			operands = []
			for subterm in self.subterms():
				if subterm.is_add():
					operands.extend(subterm.subterms())
				else:
					operands.append(subterm)
			
			if len(operands) == 0:
				return self.algebra.zero()
			elif len(operands) == 1:
				return operands[0]
			else:
				return self.algebra.sum(operands)
		
		elif self.is_mul():
			operands = []
			for subterm in self.subterms():
				if subterm.is_mul():
					operands.extend(subterm.subterms())
				else:
					operands.append(subterm)
			
			if len(operands) == 0:
				return self.algebra.one()
			elif len(operands) == 1:
				return operands[0]
			else:
				return self.algebra.product(operands)
		
		elif self.is_sub():
			assert len(self.subterms()) == 2
			a, b = self.subterms()
			return (a + (-b).flatten()).flatten()
		
		elif self.is_neg():
			flat = self
			n = 0
			while flat.is_neg():
				n += 1
				assert len(flat.subterms()) == 1
				flat = flat.subterms()[0].flatten()
			
			if n % 2 == 0:
				return flat
			elif flat.is_add():
				return self.algebra.sum(-_subterm for _subterm in flat.subterms())
			elif flat.is_mul():
				minus_one = self.algebra.const(-self.algebra.base_ring.one())
				return self.algebra.product(flat.subterms() + [minus_one])
			elif flat.is_sub():
				assert len(flat.subterms()) == 2
				a, b = flat.subterms()
				return b - a
			else:
				return -flat
		
		else:
			return self
	
	def additive_form_subterms(self):
		if self.is_sub():
			return 2
		
		elif self.is_neg():
			return self.subterms()[0].additive_form_subterms()
		
		elif self.is_mul():
			length = 1
			for subterm in self.subterms():
				if subterm.is_add():
					length *= len(subterm.subterms())
			return length
		
		else:
			return len(self.subterms())
	
	def additive_form(self):
		"Transforms the polynomial into the form `f[0, 0] * f[0, 1] * f[0, 2] * ... + f[1, 0] * f[1, 1] * ... + f[2, 0] * ... + ...`. May return a monomial, variable or a constant."
		
		if self.is_sub():
			a, b = self.subterms()
			c = self.algebra.const(-self.algebra.base_ring.one())
			if c.is_one():
				return a + b
			else:
				return a + c * b
		
		elif self.is_neg():
			a = self.subterms()[0]
			minus_one = self.algebra.const(-self.algebra.base_ring.one())
			if minus_one.is_one():
				return a
			elif a.is_add():
				return self.algebra.sum([minus_one * _subterm for _subterm in a])
			else:
				return (minus_one * a).additive_form()
		
		elif self.is_mul():
			operands = []
			for subterm in self.subterms():
				#print("for subterm", repr(subterm))
				if subterm.is_add():
					#print(" + is_add")
					operands.append(subterm.subterms())
				else:
					#print(" + not is_add")
					operands.append([subterm])
			
			#print(" --", operands)
			if not operands:
				return self.algebra.zero()
			
			addends = []
			for factors in product(*operands):
				if len(factors) == 0:
					addends.append(self.algebra.one())
				elif len(factors) == 1:
					addends.append(factors[0])
				else:
					addends.append(self.algebra.product(factors))
			
			if len(addends) == 0:
				return self.algebra.zero()
			elif len(addends) == 1:
				return addends[0]
			else:
				return self.algebra.sum(addends)
		
		else:
			return self
	
	@cached
	def sort_ordering(self):
		"String returned here affects the ordering of terms in `canonical`."
		if self.is_var():
			return "4_" + self.var_name()
		elif self.is_const():
			return '5_' + self.const_value().sort_ordering()
		else:
			if self.is_mul():
				operator = '0'
			elif self.is_neg():
				operator = '1'
			elif self.is_add():
				operator = '2'
			elif self.is_sub():
				operator = '3'
			else:
				raise RuntimeError
			return operator + "_" + "{:04d}".format(1000 - len(self.subterms())) + "_".join(_subterm.sort_ordering() for _subterm in self.subterms())
	
	def is_unordered(self):
		if self.is_add() or self.is_mul():
			current = ''
			for subterm in self.subterms():
				next_ = subterm.sort_ordering()
				if next_ < current:
					return True
				current_ = next_
			return False
		else:
			return False
	
	def order(self):
		if self.is_add():
			return self.algebra.sum(sorted(self.subterms(), key=self.__class__.sort_ordering))
		elif self.is_mul():
			return self.algebra.product(sorted(self.subterms(), key=self.__class__.sort_ordering))
		else:
			return self
	
	def has_potential_repetitions(self):
		if self.is_add() or self.is_mul():
			current = ''
			for subterm in self.subterms():
				next_ = subterm.sort_ordering()
				if next_ == current:
					return True
				current_ = next_
			return False
		else:
			return False
	
	def extract(self):
		"Transforms a polynomial of the form: `a * b + a * c + d` into `a * (b + c) + d`."
		
		if not self.is_add():
			return self
		
		addends = []
		factors = Counter()
		for monomial in self.subterms():
			if monomial.is_mul():
				addend = []
				for factor in monomial.subterms():
					#print(repr(factor))
					factors[Identical(factor)] += 1
					addend.append(Identical(factor))
				addends.append(addend)
			else:
				factors[Identical(monomial)] += 1
				addends.append([Identical(monomial)])
		
		winner = None
		winner_reduction = 0
		for factor, frequency in factors.most_common():
			if frequency < 2: break
			reduction = factor.term.circuit_size() * (frequency - 1)
			if reduction > winner_reduction:
				winner_reduction = reduction
				winner = factor
		
		if winner is None:
			return self
		factor = winner
		
		main = []
		rest = []
		for addend in addends:
			if factor in addend:
				addend.remove(factor)
				
				if len(addend) == 0:
					main.append(self.algebra.one())
				elif len(addend) == 1:
					main.append(addend[0].term)
				else:
					main.append(self.algebra.product(_factor.term for _factor in addend))
			else:
				if len(addend) == 0:
					rest.append(self.algebra.one())
				elif len(addend) == 1:
					rest.append(addend[0].term)
				else:
					rest.append(self.algebra.product(_factor.term for _factor in addend))
		
		factor_zero = factor.term.is_const() and factor.term.is_zero()
		
		if (factor_zero or not main) and not rest:
			return self.algebra.zero()
		elif not (factor_zero or not main) and not rest:
			result = factor.term * self.algebra.sum(main)
		elif (factor_zero or not main) and rest:
			result = self.algebra.sum(rest)
		else:
			result = factor.term * self.algebra.sum(main) + self.algebra.sum(rest)
		
		if result.circuit_size() <= self.circuit_size():
			return result
		else:
			return self
	
	def fold(self, v=None):
		"Transforms a polynomial `p` into the form `cls(v == 0) * p(v=0) + cls(v == 1) * p(v=1) + ...`."
		
		if v is None:
			v, _ = Counter(self.variables()).most_common()[0]
		
		print("    fold", str(v), self.circuit_size())
		
		addends = []
		for d in self.algebra.base_ring.domain():
			s = self(**{str(v):self.algebra.const(d)})
			factors = []
			g = self.algebra.base_ring.one()
			for e in self.algebra.base_ring.domain():
				if d != e:
					factors.append((v - self.algebra.const(e)).additive_form())
					g *= d - e
			factors.append(self.algebra.const(g**-1))
			f = self.algebra.product(factors)
			addends.append(f * s)
		
		result = self.algebra.sum(addends)
		result = result.fixed_point(lambda t: t.traverse_before(self.__class__.evaluate_constants).traverse_before(self.__class__.evaluate_repetitions).flatten())
		print("     fold result", result.circuit_size(), str(result))
		return result
	
	'''
		(x == 0) * (y == 0) * p(x=0, y=0) + (x == 1) * (y == 0) * p(x=1, y=0) + (x == 0) * (y == 1) * p(x=0, y=1) + (x == 1) * (y == 1) * p(x=1, y=1)
		
		(x == 0) * p(x=0) + (x == 1) * p(x=1) =
		 = (x - 1) * p(x=0) + x * p(x=1) =
		 = p(x = 0) + x * (p(x=1) - p(x=0)) =
		 = 
		
		(x - 0) * (x - 2)

		
		(a + (x == 0)) * (b + (x == 1)) = a * b + a * (x == 1) + b * (x == 0)




		p(x=0) = a * b + a = a * (b + 1)
		p(x=1) = a * b + b = (a + 1) * b

		a = p(x=0)

	'''
	
	def __repr__(self):
		if self.is_const():
			return self.__class__.__name__ + '(' + repr(self.operator) + ', [' + repr(self.const_value()) + '])'
		elif self.is_var():
			return self.__class__.__name__ + '(' + repr(self.operator) + ', [' + repr(self.var_name()) + '])'
		else:
			return self.__class__.__name__ + '(' + repr(self.operator) + ', [' + (', '.join(repr(_subterm) for _subterm in self.subterms())) + '])'
	
	def __str__(self):
		if self.is_const():
			return str(self.const_value())
		elif self.is_var():
			return self.var_name()
		elif self.is_add():
			if len(self.subterms()) == 0:
				return '+0'
			elif len(self.subterms()) == 1:
				subterm = self.subterms()[0]
				return '+' + (('(' + str(subterm) + ')') if (not subterm.is_const() and not subterm.is_var() and not subterm.is_mul()) else str(subterm))
			else:
				return ' + '.join(('(' + str(_subterm) + ')') if (not _subterm.is_const() and not _subterm.is_var() and not _subterm.is_mul()) else str(_subterm) for _subterm in self.subterms())
		elif self.is_sub():
			return ' - '.join(('(' + str(_subterm) + ')') if (not _subterm.is_const() and not _subterm.is_var() and not _subterm.is_mul()) else str(_subterm) for _subterm in self.subterms())
		elif self.is_mul():
			if len(self.subterms()) == 0:
				return '(1)'
			elif len(self.subterms()) == 1:
				subterm = self.subterms()[0]
				return '(' + str(subterm) + ')'
			else:
				terms_str = []
				
				for isubterm, exponent in Counter(Identical(_subterm) for _subterm in self.subterms()).items():
					if exponent == 1:
						exp_index = ''
					else:
						exp_index = superscript(exponent)
					
					subterm = isubterm.term
					
					if subterm.is_var() or subterm.is_const():
						terms_str.append(str(subterm) + exp_index)
					else:
						terms_str.append('(' + str(subterm) + ')' + exp_index)
				
				return '·'.join(terms_str)
		elif self.is_neg():
			subterm = self.subterms()[0]
			return '-' + (('(' + str(subterm) + ')') if (not subterm.is_const() and not subterm.is_var() and not subterm.is_mul()) else str(subterm))
		else:
			return 'Term(' + str(self.operator) + ', [' + ', '.join([str(_subterm) for _subterm in self.subterms()]) + '])'
	
	def if_smaller(self, transform):
		if self.circuit_size() <= 1:
			return self
		t = transform(self)
		if t.circuit_size() < self.circuit_size():
			return t
		else:
			return self
	
	def const_evaluation_limit(self):
		if self.is_const() or self.is_var():
			return False
		
		if len(self.variables_set()) == 0:
			return True
		
		if not (32 < self.circuit_size() <= 512):
			return False
		
		if len(self.variables_set()) <= 4:
			return True
		
		return False
	
	def fold_limit(self):
		if len(self.variables_set()) == 1 and self.circuit_size() > 5:
			return True
		return False
	
	def fold_recurse_limit(self):
		if len(self.variables_set()) >= 2 and self.circuit_size() > 7:
			return True
		return False
	
	def all_subterms(self):
		if not self.is_var() and not self.is_const():
			for subterm in self.subterms():
				yield from subterm.all_subterms()
		yield self
	
	def subterms_freq(self):
		yield from Counter(Identical(_subterm) for _subterm in self.all_subterms()).most_common()
	
	'''
	def optimized(self):
		if self.is_optimized:
			return self
		
		if self.circuit_size() <= 1:
			return self
		
		#print("optimize", self.circuit_size())
		
		inner_fp_set = {}
		def inner_step(h):
			if h.circuit_size() <= 3:
				return h
			
			if h.is_mul():
				return h
			
			try:
				return inner_fp_set[Identical(h)]
			except KeyError:
				pass
			
			#print("    inner step", h.circuit_size(), h.circuit_depth())
			
			g = h
			h = h.fixed_point(self.__class__.flatten)
			h = h.additive_form()
			h = h.extract()
			h = h.evaluate_constants()
			
			if h.circuit_size() > g.circuit_size():
				h = g
			
			inner_fp_set[Identical(g)] = h
			
			return h
		
		def outer_step(h):
			if h.circuit_size() <= 1:
				return h
			#print("  optimize outer step", h.circuit_size(), h.circuit_depth())
			
			#print("   optimize outer step evaluate constants")
			h = h.traverse_before_filtered(self.__class__.evaluate_constants, self.__class__.has_nonreduced_constants, self.__class__.has_nonreduced_constants)
			
			#print("   optimize outer step order")
			h = h.traverse_before_filtered(self.__class__.order, self.__class__.is_unordered, (lambda _t: True))
			
			#print("   optimize outer step evaluate repetitions")
			h = h.traverse_after_filtered(self.__class__.evaluate_repetitions, self.__class__.has_potential_repetitions, (lambda _t: True))
			
			#print("   optimize outer step evaluate constant term")
			h = h.traverse_before_filtered(self.__class__.evaluate_constant_term, self.__class__.const_evaluation_limit, (lambda _t: True))
			
			#print("   optimize outer step fold")
			#h = h.traverse_before_filtered(self.__class__.fold, self.__class__.fold_limit, self.__class__.fold_recurse_limit)
			
			#print("   optimize extract")
			h = h.traverse_after(inner_step)
			
			#print("   optimize outer step flatten")
			h = h.traverse_before(self.__class__.flatten)
			
			return h
		
		#print(self)
		#print("optimize", self.circuit_size(), self.circuit_depth())
		
		result = self
		
		#result = result.traverse_after(self.__class__.flatten)
		
		if result.has_nonreduced_constants():
			#print("  optimize: evaluate constants")
			result = result.traverse_before_filtered(self.__class__.evaluate_constants, self.__class__.has_nonreduced_constants, self.__class__.has_nonreduced_constants)
		
		if result.circuit_size() > 1:
			#print("  optimize: outer step")
			result = result.fixed_point(outer_step)
		
		result = result.traverse_before(self.__class__.flatten).evaluate_repetitions().evaluate_constants()
		
		result.is_optimized = True
		
		#from math import ceil
		#print(" optimize: result", self.circuit_size(), result.circuit_size(), str(ceil(100 * (self.circuit_size() - result.circuit_size()) / self.circuit_size())) + "%" if self.circuit_size() > 0 else '100%' )
		#print(" ", result)
		#print()
		return result
	'''
	
	
	def optimized(self):		
		def inner_step(term):
			orig_term = term
			term = term.additive_form()
			term = term.extract()
			if term.circuit_size() < orig_term.circuit_size():
				return term
			else:
				return orig_term
		
		def outer_step(term):
			term = term.traverse_after_filtered(inner_step, self.__class__.is_add, (lambda _t: True))
			term = term.traverse_before_filtered(self.__class__.evaluate_constants, self.__class__.has_nonreduced_constants, self.__class__.has_nonreduced_constants)
			term = term.traverse_before(self.__class__.flatten)
			return term
		
		return self.shrinking(outer_step)
	
	
	def canonical(self):
		try:
			return self.canonical_cache
		except AttributeError:
			pass
		
		result = self.algebra.sum(_monomial.flatten().evaluate_constants() for _monomial in self.monomials()).flatten().evaluate_constants()
		self.canonical_cache = result
		return result
	
	def __eq__(self, other):
		#if not (self.is_const() or self.is_var()):
		#	raise RuntimeError
		
		if self is other:
			return True
		
		if isinstance(other, Identical):
			raise ValueError("Comparing `Term` with `Identical` is an error.")
		
		try:
			if self.hash_cache != other.hash_cache:
				return False
		except AttributeError:
			pass
		
		try:
			if self.identical_hash_cache != other.identical_hash_cache:
				return False
		except AttributeError:
			pass
		
		if isinstance(other, Term):
			if Identical(self) == Identical(other):
				return True
			return Identical(other.canonical()) == Identical(self.canonical())
		else:
			if Identical(self) == Identical(self.algebra.const(other)):
				return True
			return Identical(self.algebra.const(other).canonical()) == Identical(self.canonical())
		
		return NotImplemented
	
	def __hash__(self):
		if self.is_const():
			return hash(self.const_value())
		elif self.is_var():
			return hash(self.var_name())
		
		#raise RuntimeError
		
		try:
			return self.hash_cache
		except AttributeError:
			pass
		
		c = self.canonical()
		if c.is_const():
			result = hash(c.const_value())
		else:
			result = hash(Identical(c))
		
		self.hash_cache = result
		return result


def superscript(n):
	digits = []
	while n > 0:
		digits.append(n % 10)
		n //= 10
	return ''.join(['⁰¹²³⁴⁵⁶⁷⁸⁹'[_d] for _d in reversed(digits)])



if __name__ == '__main__' and __debug__:
	t0 = Term.zero()
	t1 = Term.one()
	x = Term.var('x')
	y = Term.var('y')
	
	a = t0 + t1 - t0 * x
	b = t1 + t1 + t0 * x
	c = x * t1 + t1
	d = x * y - y * x
	e = d(x=a, y=c)
	f = x * (y + t1) + (x + t1) * (y + x + t1)
	g = f(x=e, y=d)
	h = g(x=g, y=g)
	i = h(x=h, y=h)
	j = i - t1 * i
	
	assert t0.is_zero()
	assert not t1.is_zero()
	assert not x.is_zero()
	assert not a.is_zero()
	assert b.is_zero()
	assert not c.is_zero()
	assert d.is_zero()
	assert e.is_zero()
	assert not f.is_zero()
	assert not g.is_zero()
	assert not h.is_zero()
	#assert not i.is_zero()
	#assert j.is_zero()
	
	assert not t0.is_one()
	assert t1.is_one()
	assert not x.is_one()
	assert a.is_one()
	assert not b.is_one()
	assert not c.is_one()
	assert not d.is_one()
	assert not e.is_one()
	assert not f.is_one()
	assert g.is_one()
	assert h.is_one()
	#assert i.is_one()
	#assert not j.is_one()
	
	print(a.optimized())
	print(b.optimized())
	print(c.optimized())
	print(d.optimized())
	print(e.optimized())
	print(f.optimized())
	print(g.optimized())
	print(h.optimized())
	#print()
	#print(i.circuit_size())
	#print(i.optimized())
	#print()
	#print(j.circuit_size())
	#print(j.optimized())
	
	print()
	print("a:", a.canonical())
	print("b:", b.canonical())
	print("c:", c.canonical())
	print("d:", d.canonical())
	print("e:", e.canonical())
	print("f:", f.canonical())
	print("g:", g.canonical())
	print("h:", h.canonical())
	print("i:", i.canonical())
	print("j:", j.canonical())


