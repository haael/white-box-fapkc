#!/usr/bin/python3
#-*- coding:utf8 -*-

from rings import BooleanRing
from polynomial import Polynomial
from linear import Vector, Matrix


ring = BooleanRing.get_algebra()
polynomial = Polynomial.get_algebra(base_ring=ring)
vector = Vector.get_algebra(base_ring=polynomial)
const_vector = Vector.get_algebra(base_ring=ring)
matrix = Matrix.get_algebra(base_ring=polynomial)
const_matrix = Matrix.get_algebra(base_ring=ring)

zero = ring.zero()
one = ring.one()


class Integer:
	def __init__(self, value):
		self.value = const_vector(value)
	
	def __bool__(self):
		return bool(self.value)
	
	def __int__(self):
		return int(self.value)
	
	def bit_length(self):
		return len(self.value)
	
	def __add__(self, other):
		result = vector.zero(max(len(self.value), len(other.value)) + 1)
		c = zero
		for n, (a, b) in enumerate(zip(self.value, other.value)):
			result[n] = (a + b + c).optimized()
			c = (a * b | b * c | a * c).optimized()
		return self.__class__(result)
	
	def __mul__(self, other):
		result = self.__class__(0)
		for n in range(other.bit_length()):
			result += ((other >> n) & self.__class__(1)) * (self << n)
		return result
	
	def __and__(self, other):
		raise NotImplementedError
	
	def __xor__(self, other):
		return self.__class__(self.value + other.value)


def unpack_state(state, lengths):
	raise NotImplementedError

def pack_state(variables, lengths):
	raise NotImplementedError


def sample_fn(input_stream, state=vector.zero(sum((len_a, len_b, len_c)))):
	a, b, c = unpack_state(state, (len_a, len_b, len_c))
	for char in input_stream:
		old_a = a
		a = b
		b = c
		c = old_a * char
		
		yield a + b + c + char
	state[:] = pack_state((a, b, c), (len_a, len_b, len_c))















