#!/usr/bin/python3
#-*- coding:utf8 -*-

from rings import BooleanRing
#from polynomial import Polynomial
#from linear import Vector, Matrix
from automaton import automaton_factory

Automaton = automaton_factory(BooleanRing.get_algebra())

ring = Automaton.base_ring
const_vector = Automaton.base_const_vector
const_matrix = Automaton.base_const_matrix
polynomial = Automaton.base_polynomial
vector = Automaton.base_vector
matrix = Automaton.base_matrix

zero = polynomial.zero()
one = polynomial.one()


class Integer:
	def __init__(self, value):
		self.value = value
	
	def __bool__(self):
		return bool(self.value)
	
	def __int__(self):
		return int(self.value)
	
	def bit_length(self):
		return len(self.value)
	
	def __add__(self, other):
		result = vector.zero(self.bit_length())
		c = zero
		for n, (a, b) in enumerate(zip(self.value, other.value)):
			result[n] = (a + b + c).optimized()
			c = (a * b | b * c | a * c).optimized()
		return self.__class__(result)
	
	def __mul__(self, other):
		result = self.__class__(vector.zero(self.bit_length()))
		for n in range(other.bit_length()):
			a = self.__class__(((self << n).value * other.value[n]).optimized())
			result += a
			#print(int(self << n), int(other.value[n]), int(a), int(result))
		return result
	
	def __and__(self, other):
		result = vector.zero(min(self.bit_length(), other.bit_length()))
		for n, (a, b) in enumerate(zip(self.value, other.value)):
			result[n] = (a * b).optimized()
		return self.__class__(result)
	
	def __xor__(self, other):
		return self.__class__((self.value + other.value).optimized())
	
	def __rshift__(self, n):
		return self.__class__(self.value[n:])
	
	def __lshift__(self, n):
		result = vector.zero(len(self.value) + n)
		for m in range(len(self.value)):
			result[m + n] = self.value[m]
		return self.__class__(result)
	
	def __eq__(self, other):
		all_eq = one
		for n, (a, b) in enumerate(zip(self.value, other.value)):
			bit_eq = (a + b + one).optimized()
			all_eq = (all_eq * bit_eq).optimized()
		return self.__class__(vector([all_eq] + [zero] * (self.bit_length() - 1)))
	
	def __ne__(self, other):
		any_ne = zero
		for n, (a, b) in enumerate(zip(self.value, other.value)):
			bit_ne = (a + b).optimized()
			any_ne = (any_ne | bit_ne).optimized()
		return self.__class__(vector([any_ne] + [zero] * (self.bit_length() - 1)))
	
	def __gt__(self, other):
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip(self.value, other.value))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return self.__class__(vector([self_wins.optimized()] + [zero] * (self.bit_length() - 1)))
	
	def __ge__(self, other):
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip(self.value, other.value))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return self.__class__(vector([(other_wins + one).optimized()] + [zero] * (self.bit_length() - 1)))
	
	def __lt__(self, other):
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip(self.value, other.value))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return self.__class__(vector([other_wins.optimized()] + [zero] * (self.bit_length() - 1)))
	
	def __le__(self, other):
		self_wins = zero
		other_wins = zero
		for a, b in reversed(list(zip(self.value, other.value))):
			self_wins |= (a * (b + one) * (other_wins + one)).optimized()
			other_wins |= ((a + one) * b * (self_wins + one)).optimized()
		return self.__class__(vector([(self_wins + one).optimized()] + [zero] * (self.bit_length() - 1)))
	



a = Integer(vector(ord('A'), 8))
b = Integer(vector(ord('b'), 8))
c = Integer(vector(ord(':'), 8))
d = Integer(vector(ord('0'), 8))

#print((Integer(vector(ord('a'), 8)) < Integer(vector(ord('b'), 8))).value)
#quit()


def sample_fn(input_stream, state=vector.zero(8 + 1)):
	uppercase = state[0]
	lowercase = state[1]
	numbers = state[2]
	special = state[3]
	length = Integer(state[4:8])
	
	zero = Integer(vector(0, 8))
	one = Integer(vector(1, 8))
	bit_one = polynomial.one()
	min_pass_len = Integer(vector(3, 8))
	lower_a = Integer(vector(ord('a'), 8))
	lower_z = Integer(vector(ord('z'), 8))
	upper_a = Integer(vector(ord('A'), 8))
	upper_z = Integer(vector(ord('Z'), 8))
	char_0 = Integer(vector(ord('0'), 8))
	char_9 = Integer(vector(ord('9'), 8))
	
	for symbol in input_stream:
		assert len(symbol) == 8
		char = Integer(symbol)
		
		lower_letter = ((lower_a <= char) & (char <= lower_z)).value[0]
		#print(char.value, (lower_a >= char).value)
		upper_letter = ((upper_a <= char) & (char <= upper_z)).value[0]
		digit = ((char_0 <= char) & (char <= char_9)).value[0]
		special_char = ((lower_letter + bit_one) * (upper_letter + bit_one) * (digit + bit_one)).optimized()
		
		uppercase |= upper_letter
		uppercase = uppercase.optimized()
		lowercase |= lower_letter
		lowercase = lowercase.optimized()
		numbers |= digit
		numbers = numbers.optimized()
		special |= special_char
		special = special.optimized()
		length += one * (length < min_pass_len)
		#print((length).value)
		
		pass_ok = (uppercase * lowercase * numbers * special * (length == min_pass_len).value[0])
		
		yield vector([pass_ok])
	
	state[0] = uppercase
	state[1] = lowercase
	state[2] = numbers
	state[3] = special
	state[4:8] = length.value


print([int(x) for x in sample_fn([a.value, b.value, c.value, d.value])])


argument = vector(Automaton.x[_i] for _i in range(8))
state = vector(Automaton.s[1, _i] for _i in range(9))
print(argument, state)
result = list(sample_fn([argument], state))[0]
print(type(result))

sample_fsm = Automaton(output_transition=result, state_transition=state)
#sample_fsm.optimize()

#state = vector.zero(8 + 1)
print([int(x) for x in sample_fsm([a.value, b.value, c.value, d.value])])


print(sample_fsm.output_transition.circuit_size(), sample_fsm.state_transition.circuit_size())

mixer8, unmixer8 = Automaton.fapkc0(block_size=8, memory_size=4)
mixer1, unmixer1 = Automaton.fapkc0(block_size=1, memory_size=4)

sample_homo = mixer1 @ sample_fsm @ unmixer8
print(sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size())
sample_homo.mix_states()
print(sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size())
sample_homo.optimize()
print(sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size())



