#!/usr/bin/python3
#-*- coding:utf8 -*-

from rings import BooleanRing
#from polynomial import Polynomial
#from linear import Vector, Matrix
from automaton import automaton_factory
from utils import parallel
from itertools import zip_longest


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
		
		self.b_value = value.optimized()
	
	def __and__(self, other):
		try:
			return self.__class__(self.b_value * other.b_value)
		except AttributeError:
			return NotImplemented
	
	def __or__(self, other):
		try:
			return self.__class__(self.b_value | other.b_value)
		except AttributeError:
			return NotImplemented
	
	def __xor__(self, other):
		try:
			return self.__class__(self.b_value + other.b_value)
		except AttributeError:
			return NotImplemented
	
	def __invert__(self):
		return self.__class__(self.b_value + one)
	
	def __add__(self, other):
		return NotImplemented
	
	def __sub__(self, other):
		return NotImplemented
	
	def __mul__(self, other):
		return NotImplemented
	
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
			self.i_value = vector(value, value.bit_length())
			return
		except (TypeError, AttributeError):
			pass
		
		try:
			self.i_value = vector([value.b_value])
			return
		except AttributeError:
			pass
		
		self.i_value = value.optimized()
	
	def __bool__(self):
		return bool(self.i_value)
	
	def __int__(self):
		return int(self.i_value)
	
	def bit_length(self):
		return len(self.i_value)
	
	def __add__(self, other):
		other = self.__class__(other)
		result = vector.zero(max(self.bit_length(), other.bit_length()) + 1)
		c = zero
		for n, (a, b) in enumerate(zip_longest(self.i_value, other.i_value, fillvalue=zero)):
			result[n] = (a + b + c).optimized()
			c = (a * b | b * c | a * c).optimized()
		return self.__class__(result)
	
	def __mul__(self, other):
		other = self.__class__(other)
		result = self.__class__(vector.zero(self.bit_length()))
		for n in range(other.bit_length()):
			a = self.__class__(((self << n).i_value * other.i_value[n]).optimized())
			result += a
			#print(int(self << n), int(other.i_value[n]), int(a), int(result))
		return result
	
	def __and__(self, other):
		other = self.__class__(other)
		result = vector.zero(min(self.bit_length(), other.bit_length()))
		for n, (a, b) in enumerate(zip(self.i_value, other.i_value)):
			result[n] = a * b
		return self.__class__(result)
	
	def __xor__(self, other):
		return self.__class__(self.i_value + other.i_value)
	
	def __rshift__(self, n):
		return self.__class__(self.i_value[n:])
	
	def __lshift__(self, n):
		result = vector.zero(len(self.i_value) + n)
		for m in range(len(self.i_value)):
			result[m + n] = self.i_value[m]
		return self.__class__(result)
	
	def __eq__(self, other):
		other = self.__class__(other)
		all_eq = one
		for n, (a, b) in enumerate(zip(self.i_value, other.i_value)):
			bit_eq = (a + b + one).optimized()
			all_eq = (all_eq * bit_eq).optimized()
		return Boolean(all_eq)
	
	def __ne__(self, other):
		any_ne = zero
		for n, (a, b) in enumerate(zip(self.i_value, other.i_value)):
			bit_ne = (a + b).optimized()
			any_ne = (any_ne | bit_ne).optimized()
		return Boolean(any_ne)
	
	def __gt__(self, other):
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip(self.i_value, other.i_value))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return Boolean(self_wins.optimized())
	
	def __ge__(self, other):
		other = self.__class__(other)
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip(self.i_value, other.i_value))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return Boolean((other_wins + one).optimized())
	
	def __lt__(self, other):
		other = self.__class__(other)
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip(self.i_value, other.i_value))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return Boolean(other_wins.optimized())
	
	def __le__(self, other):
		other = self.__class__(other)
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip(self.i_value, other.i_value))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return Boolean((self_wins + one).optimized())
	


if __name__ == '__main__':	
	
	def sample_fn(input_stream, state=vector.zero(8 + 1)):
		uppercase = Boolean(state[0])
		lowercase = Boolean(state[1])
		numbers = Boolean(state[2])
		special = Boolean(state[3])
		length = Integer(state[4:8])
		
		bit_one = polynomial.one()
		
		min_pass_len = 3
		lower_a = ord('a')
		lower_z = ord('z')
		upper_a = ord('A')
		upper_z = ord('Z')
		char_0 = ord('0')
		char_9 = ord('9')
		
		for symbol in input_stream:
			assert len(symbol) <= 8
			char = Integer(symbol)
			
			lower_letter = (lower_a <= char) & (char <= lower_z)
			upper_letter = (upper_a <= char) & (char <= upper_z)
			digit = (char_0 <= char) & (char <= char_9)
			special_char = ~lower_letter & ~upper_letter & ~digit
			
			uppercase |= upper_letter
			lowercase |= lower_letter
			numbers |= digit
			special |= special_char
			length += (length < min_pass_len)
			length &= 0b1111
			
			#print(int(length))
			
			pass_ok = uppercase & lowercase & numbers & special & (length == min_pass_len)
			
			yield vector([pass_ok.b_value])
			
			assert length.bit_length() <= 4
		
		state[0] = uppercase.b_value
		state[1] = lowercase.b_value
		state[2] = numbers.b_value
		state[3] = special.b_value
		state[4:8] = length.i_value
	
	print("converting function to automaton")
	
	a = vector(ord('A'), 8)
	b = vector(ord('b'), 8)
	c = vector(ord(':'), 8)
	d = vector(ord('0'), 8)

	
	source_output = [int(x) for x in sample_fn([a, b, c, d])]
	print("source function output:", source_output)

	argument = vector(Automaton.x[_i] for _i in range(8))
	state = vector(Automaton.s[1, _i] for _i in range(9))
	result = list(sample_fn([argument], state))[0]
		
	sample_fsm = Automaton(output_transition=result, state_transition=state)
	fsm_output = [int(x) for x in sample_fsm([a, b, c, d])]
	print("plain automaton output:", fsm_output)
	
	assert source_output == fsm_output

	print("size of plain automaton:", sample_fsm.output_transition.circuit_size(), sample_fsm.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_fsm.state_transition])
	
	if __debug__: print("\n *** WARNING: try running the script with optimization flag `-O` to speed up obfuscated automaton generation ***\n")
	
	with parallel():
		print()
		print("obfuscating automaton")
		
		print("generating FAPKC keys")
		mixer8, unmixer8 = Automaton.fapkc0(block_size=8, memory_size=4)
		mixer1, unmixer1 = Automaton.fapkc0(block_size=1, memory_size=4)
		
		unmixer8.optimize()
		mixer1.optimize()
		
		sample_homo = mixer1 @ sample_fsm @ unmixer8
		print("size of raw homomorphic automaton:", sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_homo.state_transition])
		sample_homo.optimize()
		print("after optimization:", sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_homo.state_transition])
		sample_homo.mix_states()
		print("size of mixed homomorphic automaton:", sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_homo.state_transition])
		sample_homo.optimize()
		print("after optimization:", sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_homo.state_transition])
	
	
	
	