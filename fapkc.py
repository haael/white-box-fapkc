#!/usr/bin/python3


from enum import Enum
from collections import deque
from random import randrange

from utils import cached
from fields import Polynomial as AbstractPolynomial
from algebra import *
from machines import *
from aes import *


class Polynomial(AbstractPolynomial):
	Field = Rijndael
	
	def __init__(self, *coefficients):
		if len(coefficients) > self.Field.field_size:
			short = coefficients[:self.Field.field_size]
			for n, x in enumerate(coefficients[self.Field.field_size:]):
				short[n % self.Field.field_size] += x
			super().__init__(*short)
		else:
			super().__init__(*coefficients)


class Transducer1:
	@property
	@cached
	def Field(self):
		return self.__in_transition[0].Field
	
	def __init__(self, in_transition, out_transition=None):
		self.__in_transition = in_transition
		self.__out_transition = out_transition
	
	def __call__(self, i):
		if self.__out_transition is not None:
			d = len(self.__out_transition) - 1
		else:
			d = 0
		co = deque([self.Field.zero()] * d)
		
		e = len(self.__in_transition)
		ci = deque([self.Field.zero()] * e)
		
		s = []
		for i0 in i:
			s.clear()
			
			ci.append(i0)
			ci.popleft()
			
			for k, f in enumerate(self.__in_transition):
				if f is None: continue
				v = ci[len(ci) - 1 - k]
				s.append(f(v))
			
			if self.__out_transition is not None:
				for k, f in enumerate(self.__out_transition):
					if k == 0 and f is not None: raise ValueError("First output function must be None.")
					if f is None: continue
					v = co[len(co) - 1 - k]
					s.append(f(v))
			
			o0 = self.Field.sum(s)
			
			co.append(o0)
			co.popleft()
			
			yield o0


class Transducer:
	@property
	@cached
	def Field(self):
		return self.__in_transition.Field
	
	def __init__(self, in_transition, out_transition=None):
		self.__in_transition = in_transition
		self.__out_transition = out_transition
	
	def __call__(self, i):
		if self.__out_transition is not None:
			if self.__out_transition.output_size != 1:
				raise ValueError
			d = self.__out_transition.input_size - 1
			co = Vector.zero(d, list, self.Field)
		
		if self.__in_transition.output_size != 1:
			raise ValueError
		e = self.__in_transition.input_size
		ci = Vector.zero(e, list, self.Field)
		
		for i0 in i:
			ci = (Vector([i0]) | ci)[:e]
			
			o0 = self.__in_transition(ci)[0]
			if self.__out_transition is not None:
				o0 += self.__out_transition(co)[0]
				co = (Vector([o0]) | co)[:d]
			
			yield o0


def function_image(f):
	return frozenset(f(_x) for _x in Rijndael.domain())


def function_roots(f):
	return frozenset(_x for _x in Rijndael.domain() if not f(_x))


def left_zero_divisor(P):
	_0 = P.zero_element()
	_1 = P.one_element()
	
	X = Polynomial(_1, _0)
	R = Polynomial(_1)
	for r in function_image(P):
		Rr = X - Polynomial(r)
		assert Rr(r) == _0
		R *= Rr
	
	R = Linear([R[Rijndael.field_base ** _n] for _n in range(Rijndael.field_power)])
	
	if __debug__:
		image = function_image(P)
		
		for r in image:
			assert R(r) == _0
		
		for x in Rijndael.domain():
			assert P(x) in image
			assert R(P(x)) == _0
	
	assert R @ P == Lo
	
	return R


def random_singular():
	roots = frozenset()
	while len(roots) < 4:
		P = Linear.random(list, Rijndael, randrange)
		roots = function_roots(P)
	
	roots = frozenset()
	while len(roots) < 4:
		Q = Linear.random(list, Rijndael, randrange)
		roots = function_roots(Q)
	
	roots = frozenset()
	while len(roots) < 4:
		R = Linear.random(list, Rijndael, randrange)
		roots = function_roots(R)
	
	roots = frozenset()
	while len(roots) < 4:
		S = Linear.random(list, Rijndael, randrange)
		roots = function_roots(S)
	
	return S @ R @ Q @ P


def random_invertible():
	while True:
		P = Linear.random(list, Rijndael, randrange)
		try:
			P.inverse()
		except ArithmeticError:
			pass
		else:
			return P


def fapkc_delay_1():
	while True:
		A = random_singular()
		P = Linear.random(list, Rijndael, randrange) @ left_zero_divisor(A)
		assert P @ A == Lo
		
		B = random_singular()
		Q = Linear.random(list, Rijndael, randrange) @ left_zero_divisor(B)
		assert Q @ B == Lo
		
		M = P @ B + Q @ A
		print(len(function_roots(M)))
		if len(function_roots(M)) > 1:
			continue
		
		try:
			Mi = M.inverse()
		except ArithmeticError:
			continue
		
		return A, B, Mi @ P, Mi @ Q


def fapkc_delay_n(d):
	d += 1
	while True:
		A = [random_singular() for _n in range(d)]
		P = [left_zero_divisor(A[_n]) for _n in range(d)]
		PA = [P[_n] @ A[d - 1 -_n] for _n in range(d)]
		
		for m in range(10):
			R = [Linear.random(list, Rijndael, randrange) for _n in range(d)]
			M = sum((R[_n] @ PA[_n] for _n in range(d)), Linear.zero(list, Rijndael))
			
			print(len(function_roots(M)))
			
			try:
				Mi = M.inverse()
			except ArithmeticError:
				continue
			
			return A, [Mi @ R[_n] @ P[_n] for _n in range(d)]

'''

def fapkc_inverse_check(A, B, P, Q, i, o):
	for t in range(len(i)):
		assert sum(A[_n](i[t - _n]) for _n in range(d)) == sum(B[_n](o[t - _n]) for _n in range(d))
	
	PA = 0
	for m in range(d):
		for n in range(d):
			PA[_m + _n] += P[_m] @ A[_n]
	assert PA[d] == 1
	
	P[d - 1] @ A[d - 1] == 0

	P[d - 2] @ A[d - 1] + P[d - 1] @ A[d - 2] == 0
	P[d - 2] @ A[d - 1] == -P[d - 1] @ A[d - 2]

	lzd1 @ A[d - 1] = 0
	lzd2 @ -P[d - 1] @ A[d - 2] @ A[d - 1] = 0

	(lzd1 + lzd2 @ -P[d - 1] @ A[d - 2]) @ A[d - 1] = lzd1 @ A[d - 1] + lzd2 @ -P[d - 1] @ A[d - 2] @ A[d - 1]
'''


if __name__ == '__main__':	
	#_0 = Rijndael.zero()
	#_1 = Rijndael.one()
	
	Lo = Linear.zero(list, Rijndael)
	Li = Linear.one(list, Rijndael)
	
	(A, B), (P, Q) = fapkc_delay_n(1)
	
	A = Transducer(LinearCircuit({(0, 0):A, (0, 1):B}))
	B = Transducer(LinearCircuit({(0, 0):P, (0, 1):Q}))
	
	i = [Rijndael.random(randrange) for _i in range(10)]
	o = A(i)
	j = B(A(i))
	
	for n, (x, y, z) in enumerate(zip(i, o, j)):
		print(n, x, y, z)
	
	quit()
	
	(A, B, C), (P, Q, R) = random_delay_2()
	assert A @ P == Lo
	assert A @ Q + B @ P == Lo
	M = A @ R + B @ Q + C @ P


	
	print(La[0]._Linear__f)
	print(La[1]._Linear__f)
	print(Lb[0]._Linear__f)
	print(Lb[1]._Linear__f)
	print(Lc[0]._Linear__f)
	print(Lc[1]._Linear__f)
	
	Rijndael.__add__ = lambda x, y: Rijndael(SymbolicValue._fun_uint('Rijndael.__add__')(symbolize(x)[1], symbolize(y)[1]))
	Rijndael.__sub__ = lambda x, y: Rijndael(SymbolicValue._fun_uint('Rijndael.__sub__')(symbolize(x)[1], symbolize(y)[1]))
	Rijndael.__mul__ = lambda x, y: Rijndael(SymbolicValue._fun_uint('Rijndael.__mul__')(symbolize(x)[1], symbolize(y)[1]))
	Rijndael.__truediv__ = lambda x, y: Rijndael(SymbolicValue._fun_uint('Rijndael.__truediv__')(symbolize(x)[1], symbolize(y)[1]))
	Rijndael.__pow__ = lambda x, y: Rijndael(SymbolicValue._fun_uint('Rijndael.__pow__')(symbolize(x)[1], symbolize(y)[1]))
	Rijndael.sum = lambda a: Rijndael(SymbolicValue._fun_uint('Rijndael.sum')([symbolize(_x)[1] for _x in a]))
	
	Linear.__call__ = lambda x, y: Rijndael(SymbolicValue._fun_uint('Linear.__call__')(symbolize(x)[1], symbolize(y)[1]))
	#Linear.__add__ = lambda x, y: Linear(SymbolicValue._fun_list_uint('Linear.__add__', Rijndael.field_power)(SymbolicValue._fun_list_uint('Linear', Rijndael.field_power)(id(x)), SymbolicValue._fun_list_uint('Linear', Rijndael.field_power)(id(y))))
	#Linear.__neg__ = lambda x: Linear(SymbolicValue._fun_list_uint('Linear.__neg__', Rijndael.field_power)(SymbolicValue._fun_list_uint('Linear', Rijndael.field_power)(id(x))))
	#Linear.__matmul__ = lambda x, y: Linear(SymbolicValue._fun_list_uint('Linear.__matmul__', Rijndael.field_power)(SymbolicValue._fun_list_uint('Linear', Rijndael.field_power)(id(x)), SymbolicValue._fun_list_uint('Linear', Rijndael.field_power)(id(y))))
	

	#La[0] = SymbolicValue._fun_uint('La[0]')
	#La[1] = SymbolicValue._fun_uint('La[1]')
	#Lb[0] = SymbolicValue._fun_uint('Lb[0]')
	#Lb[1] = SymbolicValue._fun_uint('Lb[1]')
	#Lc[0] = SymbolicValue._fun_uint('Lc[0]')
	#Lc[1] = SymbolicValue._fun_uint('Lc[1]')
	
	
	A = Transducer([(lambda x: Rijndael(SymbolicValue._fun_uint('Lb[0] @ La[0]')(symbolize(x)[1]))), (lambda x: Rijndael(SymbolicValue._fun_uint('Lb[1] @ La[1]')(symbolize(x)[1])))], [], Rijndael)
	B = Transducer([None, (lambda x: Rijndael(SymbolicValue._fun_uint('Lc[0]')(symbolize(x)[1]))), (lambda x: Rijndael(SymbolicValue._fun_uint('Lc[1]')(symbolize(x)[1])))], [None, (lambda x: Rijndael(SymbolicValue._fun_uint('-(Lc[0] * Lb[0] * La[0])')(symbolize(x)[1]))), None, (lambda x: Rijndael(SymbolicValue._fun_uint('-(Lc[1] * Lb[1] * La[1])')(symbolize(x)[1])))], Rijndael)

	#i = Sequence._stream(list(Rijndael.domain()))
	i = Sequence._stream([SymbolicValue._arg_uint(_i) for _i in range(100)])
	
	o = list(A(i))
	j = list(B(o))
	
	for n, (x, y, z) in enumerate(zip(i, o, j)):
		print(n)
		symbolize(x)[1]._print_tree()
		symbolize(y)[1]._print_tree()
		symbolize(z)[1]._print_tree()
		if n >= 3:
			break



