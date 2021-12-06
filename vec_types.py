#!/usr/bin/python3
#-*- coding:utf8 -*-


"Helper classes that allow implementing finite automata using standard Python syntax."


from rings import BooleanRing
from automaton import automaton_factory
from utils import parallel
from itertools import zip_longest


__all__ = 'Boolean', 'Integer', 'Array'


Automaton = automaton_factory(BooleanRing.get_algebra())

ring = Automaton.base_ring
const_vector = Automaton.base_const_vector
const_matrix = Automaton.base_const_matrix
polynomial = Automaton.base_polynomial
vector = Automaton.base_vector
matrix = Automaton.base_matrix

zero = polynomial.zero()
one = polynomial.one()


class Boolean:
	"A class performing boolean operations using an element of boolean field as backing. Can be used for symbolic tracing."
	
	def __init__(self, value):
		try:
			self.b_value = value.b_value
			return
		except AttributeError:
			pass
		
		try:
			self.b_value = polynomial(value.optimized())
			return
		except AttributeError:
			pass
		
		self.b_value = polynomial.const(ring(bool(value)))
	
	def __str__(self):
		try:
			return str(bool(self))
		except ValueError:
			return f'Boolean({str(self.b_value)})'
	
	def __bool__(self):
		if self.b_value.is_zero():
			return False
		elif self.b_value.is_one():
			return True
		else:
			raise ValueError("`Boolean` value not true nor false.")
	
	def __and__(self, other):
		if hasattr(other, 'i_value'):
			return NotImplemented
		other = self.__class__(other)
		return self.__class__(self.b_value * other.b_value)
	
	def __or__(self, other):
		if hasattr(other, 'i_value'):
			return NotImplemented
		other = self.__class__(other)
		return self.__class__(self.b_value | other.b_value)
	
	def __xor__(self, other):
		if hasattr(other, 'i_value'):
			return NotImplemented
		other = self.__class__(other)
		return self.__class__(self.b_value + other.b_value)
	
	def __invert__(self):
		return self.__class__(self.b_value + one)
	
	def __add__(self, other):
		return NotImplemented
	
	def __sub__(self, other):
		return NotImplemented
	
	def __mul__(self, other):
		if hasattr(other, 'i_value'):
			return NotImplemented
		else:
			return self * Integer(other)
	
	def __lshift__(self, other):
		return Integer(vector([self.b_value])) << other
	
	def __rshift__(self, other):
		return self & (other > 0)


class Integer:
	"A class performing arithmetic operations using a vector of elements of boolean field as backing. Can be used for symbolic tracing."
	
	def __init__(self, value):
		try:
			self.i_value = value.i_value
			return
		except AttributeError:
			pass
		
		try:
			self.i_value = vector(value, value.bit_length()).optimized()
			return
		except (TypeError, AttributeError):
			pass
		
		try:
			self.i_value = vector([value.b_value]).optimized()
			return
		except AttributeError:
			pass
		
		self.i_value = value.optimized()
	
	def __str__(self):
		try:
			return hex(int(self))
		except ValueError:
			return f'Integer({", ".join([str(_x) for _x in self.i_value])})'
	
	def __bool__(self):
		b = Boolean(True)
		for d in self.i_value:
			b &= d
		return bool(b)
	
	def __int__(self):
		return int(self.i_value)
	
	def bit_length(self):
		return len(self.i_value)
	
	def __add__(self, other):
		other = self.__class__(other)
		result = vector.zero(max(self.bit_length(), other.bit_length()) + 1)
		c = zero
		for n, (a, b) in enumerate(zip_longest(self.i_value, other.i_value, fillvalue=zero)):
			result[n] = (a + b + c)
			c = (a * b | b * c | a * c).optimized()
		
		if(result[-1].optimized().is_zero()):
			result = result[:-1]
		
		return self.__class__(result)
	
	def __radd__(self, other):
		return self + self.__class__(other)
	
	def __sub__(self, other):
		minus_1 = self.__class__(vector([one] * self.bit_length()))
		return (self + other * minus_1) & minus_1
	
	def __mul__(self, other):
		other = self.__class__(other)
		result = self.__class__(vector.zero(self.bit_length()))
		for n in range(other.bit_length()):
			a = self.__class__(((self << n).i_value * other.i_value[n]))
			result += a
			#print(int(self << n), int(other.i_value[n]), int(a), int(result))
		return result
	
	def __rmul__(self, other):
		return self * self.__class__(other)
	
	def __and__(self, other):
		other = self.__class__(other)
		result = vector.zero(min(self.bit_length(), other.bit_length()))
		for n, (a, b) in enumerate(zip(self.i_value, other.i_value)):
			result[n] = a * b
		return self.__class__(result)
	
	def __xor__(self, other):
		other = self.__class__(other)

		if len(self.i_value) < len(other.i_value):
			i_ext = vector.zero(len(other.i_value) - len(self.i_value))
		else:
			i_ext = vector.zero(0)

		if len(self.i_value) > len(other.i_value):
			o_ext = vector.zero(len(self.i_value) - len(other.i_value))
		else:
			o_ext = vector.zero(0)
		
		return self.__class__((self.i_value | i_ext) + (other.i_value | o_ext))
	
	def __rxor__(self, other):
		return self ^ self.__class__(other)
	
	def __rshift__(self, n):
		# TODO: support variable shifts
		try:
			return self.__class__(self.i_value[n:])
		except IndexError:
			return self.__class__(0)
	
	def __lshift__(self, n):
		# TODO: support variable shifts
		result = vector.zero(len(self.i_value) + n)
		for m in range(len(self.i_value)):
			result[m + n] = self.i_value[m]
		return self.__class__(result)
	
	def __eq__(self, other):
		other = self.__class__(other)
		all_eq = one
		for n, (a, b) in enumerate(zip_longest(self.i_value, other.i_value, fillvalue=zero)):
			bit_eq = (a + b + one)
			all_eq = (all_eq * bit_eq).optimized()
		return Boolean(all_eq)
	
	def __ne__(self, other):
		other = self.__class__(other)
		any_ne = zero
		for n, (a, b) in enumerate(zip_longest(self.i_value, other.i_value, fillvalue=zero)):
			bit_ne = (a + b)
			any_ne = (any_ne | bit_ne).optimized()
		return Boolean(any_ne)
	
	def __gt__(self, other):
		other = self.__class__(other)
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip_longest(self.i_value, other.i_value, fillvalue=zero))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return Boolean(self_wins)
	
	def __ge__(self, other):
		other = self.__class__(other)
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip_longest(self.i_value, other.i_value, fillvalue=zero))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return Boolean(other_wins + one)
	
	def __lt__(self, other):
		other = self.__class__(other)
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip_longest(self.i_value, other.i_value, fillvalue=zero))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return Boolean(other_wins)
	
	def __le__(self, other):
		other = self.__class__(other)
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip_longest(self.i_value, other.i_value, fillvalue=zero))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return Boolean(self_wins + one)
	
	def __str__(self):
		return str(self.i_value)
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + repr(self.i_value) + ')'



class Array:
	"This class transforms a list of `Integer` values into an equivalent circuit that can be addressed using `Integer`. Behaves like an immutable list in the code."
	
	def __init__(self, array):
		"Compile the object from a collection of elements. This may take a long time."
		self.index = Integer(vector([polynomial.var(f'index_{_n}') for _n in range((len(array) - 1).bit_length())]))
		circuit = Integer(0)
		for n, element in enumerate(array):
			circuit ^= (self.index == Integer(n)) * Integer(element)
		self.circuit = circuit
	
	def __getitem__(self, index):
		"Get item at the specified position. Index may be the `Integer` class and does not need to be constant. If the position is larger than the array size, the result is undefined."
		subst = {}
		for n in range(self.index.bit_length()):
			i = (Integer(index) >> n).i_value
			subst[f'index_{n}'] = i[0] if len(i) else zero
		return Integer(self.circuit.i_value(**subst))




