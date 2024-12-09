#!/usr/bin/python3


from enum import Enum
from collections import deque, Counter
from random import randrange, sample
from pickle import load as pickle_load, dump as pickle_dump, PickleError
from pathlib import Path
from itertools import product

from utils import cached
from algebra import *
from machines import *
from aes import *


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
				raise ValueError(f"Out transition output size must be 1 (got {self.__out_transition.output_size}).")
			d = self.__out_transition.input_size
			co = Vector.zero(d, list, self.Field)
		
		if self.__in_transition.output_size != 1:
			raise ValueError(f"In transition output size must be 1 (got {self.__in_transition.output_size}).")
		e = self.__in_transition.input_size
		ci = Vector.zero(e, list, self.Field)
		
		for i0 in i:
			ci = (Vector([i0]) | ci)[:e]
			
			o0 = self.__in_transition(ci)[0]
			if self.__out_transition is not None:
				o0 += self.__out_transition((Vector([self.Field.zero()]) | co)[:d])[0]
				co = (Vector([o0]) | co)[:d]
			
			yield o0


def function_image(f):
	return frozenset(f(_x) for _x in Rijndael.domain())


def function_roots(f):
	return frozenset(_x for _x in Rijndael.domain() if not f(_x))


def left_zero_divisor(P):
	_0 = P.zero_element()
	_1 = P.one_element()
	
	X = UnivariatePolynomial([_0, _1] + [_0] * (P.Field.field_size - 3))
	R = UnivariatePolynomial([_1] + [_0] * (P.Field.field_size - 2))
	for r in function_image(P):
		Rr = X - UnivariatePolynomial([r] + [_0] * (P.Field.field_size - 2))
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


def right_zero_divisor(P):
	Q = Linear.zero(list, P.Field)
	for rt in function_roots(P):
		while True:
			L = random_singular(128)
			for p in P.Field.domain():
				r = L(p)
				if r:
					break
			else:
				continue
			break
		L *= rt / r
		Q += L
	
	assert function_image(Q) <= function_roots(P)
	return Q


def random_invertible():
	while True:
		P = Linear.random(list, Rijndael, randrange)
		if len(function_roots(P)) == 1:
			return P


def random_singular_nl(r):
	LD = random_singular(r)
	q = {}
	for i in range(Rijndael.field_power):
		L = LD @ random_invertible()
		for j in range(Rijndael.field_power):
			q[i, j] = L.linear_coefficient(j)
	assert len(q) == Rijndael.field_power ** 2
	return Quadratic([Linear([q[i, j] for j in range(Rijndael.field_power)]) for i in range(Rijndael.field_power)])


one_polynomials = {}

def one_polynomial(z):
	try:
		return one_polynomials[z]
	except KeyError:
		pass
	
	_0 = Rijndael.zero()
	_1 = Rijndael.one()
	
	X = Polynomial(_1, _0)
	P = Polynomial(_1)
	for a in Rijndael.domain():
		if a == z: continue
		P *= X - Polynomial(a)
	P *= Polynomial(P(z)**-1)
	
	one_polynomials[z] = P
	return P


def synthesize(f):
	_0 = Rijndael.zero()
	_1 = Rijndael.one()
	
	X = Polynomial(_1, _0)
	Q = Polynomial(_0)
	for x in Rijndael.domain():
		y = f[x]
		print("synthesize", x, y)
		
		P = one_polynomial(x) * Polynomial(y)
		
		Q += P
	
	return Q


try:
	with Path('rijndael_bits.pickle').open('rb') as fd:
		rijndael_bits = pickle_load(fd)

except (PickleError, IOError, EOFError):
	_0 = Rijndael.zero()
	_1 = Rijndael.one()
	_2 = Rijndael(2)
	
	rijndael_bit_0 = {}
	rijndael_bit_1 = {}
	rijndael_bit_2 = {}
	rijndael_bit_3 = {}
	rijndael_bit_4 = {}
	rijndael_bit_5 = {}
	rijndael_bit_6 = {}
	rijndael_bit_7 = {}
	
	for n in range(Rijndael.field_size):
		r = Rijndael(n)
		rijndael_bit_0[r] = _2**0 if ((n >> 0) & 1) else _0
		rijndael_bit_1[r] = _2**1 if ((n >> 1) & 1) else _0
		rijndael_bit_2[r] = _2**2 if ((n >> 2) & 1) else _0
		rijndael_bit_3[r] = _2**3 if ((n >> 3) & 1) else _0
		rijndael_bit_4[r] = _2**4 if ((n >> 4) & 1) else _0
		rijndael_bit_5[r] = _2**5 if ((n >> 5) & 1) else _0
		rijndael_bit_6[r] = _2**6 if ((n >> 6) & 1) else _0
		rijndael_bit_7[r] = _2**7 if ((n >> 7) & 1) else _0
	
	rijndael_bit_0 = synthesize(rijndael_bit_0)
	rijndael_bit_1 = synthesize(rijndael_bit_1)
	rijndael_bit_2 = synthesize(rijndael_bit_2)
	rijndael_bit_3 = synthesize(rijndael_bit_3)
	rijndael_bit_4 = synthesize(rijndael_bit_4)
	rijndael_bit_5 = synthesize(rijndael_bit_5)
	rijndael_bit_6 = synthesize(rijndael_bit_6)
	rijndael_bit_7 = synthesize(rijndael_bit_7)
	
	rijndael_bit_0 = Linear([rijndael_bit_0[Rijndael.field_base ** _k] for _k in range(Rijndael.field_power)])
	rijndael_bit_1 = Linear([rijndael_bit_1[Rijndael.field_base ** _k] for _k in range(Rijndael.field_power)])
	rijndael_bit_2 = Linear([rijndael_bit_2[Rijndael.field_base ** _k] for _k in range(Rijndael.field_power)])
	rijndael_bit_3 = Linear([rijndael_bit_3[Rijndael.field_base ** _k] for _k in range(Rijndael.field_power)])
	rijndael_bit_4 = Linear([rijndael_bit_4[Rijndael.field_base ** _k] for _k in range(Rijndael.field_power)])
	rijndael_bit_5 = Linear([rijndael_bit_5[Rijndael.field_base ** _k] for _k in range(Rijndael.field_power)])
	rijndael_bit_6 = Linear([rijndael_bit_6[Rijndael.field_base ** _k] for _k in range(Rijndael.field_power)])
	rijndael_bit_7 = Linear([rijndael_bit_7[Rijndael.field_base ** _k] for _k in range(Rijndael.field_power)])
	
	rijndael_bits = []
	rijndael_bits.append(rijndael_bit_0)
	rijndael_bits.append(rijndael_bit_1)
	rijndael_bits.append(rijndael_bit_2)
	rijndael_bits.append(rijndael_bit_3)
	rijndael_bits.append(rijndael_bit_4)
	rijndael_bits.append(rijndael_bit_5)
	rijndael_bits.append(rijndael_bit_6)
	rijndael_bits.append(rijndael_bit_7)
	
	with Path('rijndael_bits.pickle').open('wb') as fd:
		pickle_dump(rijndael_bits, fd)
	
	del rijndael_bit_0, rijndael_bit_1, rijndael_bit_2, rijndael_bit_3, rijndael_bit_4, rijndael_bit_5, rijndael_bit_6, rijndael_bit_7


'''
print(rijndael_bits[0])
print(rijndael_bits[1])
print(rijndael_bits[2])
print(rijndael_bits[3])
print(rijndael_bits[4])
print(rijndael_bits[5])
print(rijndael_bits[6])
print(rijndael_bits[7])
'''


assert rijndael_bits[0] @ rijndael_bits[0] == rijndael_bits[0]
assert rijndael_bits[1] @ rijndael_bits[1] == rijndael_bits[1]
assert rijndael_bits[2] @ rijndael_bits[2] == rijndael_bits[2]
assert rijndael_bits[3] @ rijndael_bits[3] == rijndael_bits[3]
assert rijndael_bits[4] @ rijndael_bits[4] == rijndael_bits[4]
assert rijndael_bits[5] @ rijndael_bits[5] == rijndael_bits[5]
assert rijndael_bits[6] @ rijndael_bits[6] == rijndael_bits[6]
assert rijndael_bits[7] @ rijndael_bits[7] == rijndael_bits[7]


assert (rijndael_bits[0] + rijndael_bits[1]) @ (rijndael_bits[0] + rijndael_bits[1]) == rijndael_bits[0] + rijndael_bits[1]


def random_singular(nr):
	_0 = Rijndael.zero()
	_1 = Rijndael.one()
	
	domain = frozenset(Rijndael.domain())
	P = Linear([_1] + [_0] * (Rijndael.field_power - 1))
	roots = function_roots(P)
	
	while len(roots) < nr:
		pr = sorted(domain - roots, key=int)
		x = pr[randrange(len(pr))]
		R = random_invertible()
		P = Linear([-R(P(x)), _1] + [_0] * (Rijndael.field_power - 2)) @ R @ P
		roots = function_roots(P)
	
	return P @ random_invertible()


def fapkc_generate_i_1():
	while True:
		P = random_invertible()
		try:
			Pi = P.inverse()
		except ArithmeticError:
			continue
		break
	
	while True:
		Q = random_invertible()
		try:
			Qi = Q.inverse()
		except ArithmeticError:
			continue
		break
		
	X = sum(rijndael_bits[:4], Lo)
	Y = sum(rijndael_bits[4:], Lo)
	
	assert X @ X == X
	assert Y @ Y == Y
	assert X @ Y == Y @ X == Lo
	assert X + Y == Li
	
	B0 = Qi @ X @ P
	A0 = Pi @ Y @ Q
	B1 = Qi @ Y @ P
	A1 = Pi @ X @ Q
	
	assert B0 @ A0 == Lo
	assert B0 @ A1 + B1 @ A0 == Li
	assert B1 @ A1 == Lo
	
	return [A0, A1], [B0, B1]


def fapkc_generate_i(d):
	if d == 1:
		return fapkc_generate_i_1()
	else:
		while True:
			A, B = fapkc_generate_i(d // 2)
			
			if __debug__:
				d1 = d // 2
				for m in range(d1 + 1):
					assert sum((B[_k] @ A[m - 1 - _k] for _k in range(m)), Lo) == Lo
				assert sum((B[_k] @ A[d1 - _k] for _k in range(d1 + 1)), Lo) == Li, str(sum((B[_k] @ A[d1 - _k] for _k in range(d1 + 1)), Lo))
			
			C, D = fapkc_generate_i(d - d // 2)
			
			if __debug__:
				d2 = d - d // 2
				for m in range(d2 + 1):
					assert sum((D[_k] @ C[m - 1 - _k] for _k in range(m)), Lo) == Lo
				assert sum((D[_k] @ C[d2 - _k] for _k in range(d2 + 1)), Lo) == Li, str(sum((D[_k] @ C[d2 - _k] for _k in range(d2 + 1)), Lo))
			
			M = [Lo for m in range(d + 1)]
			for k in range(len(A)):
				for l in range(len(C)):
					M[k + l] += C[l] @ A[k]
			
			N = [Lo for m in range(d + 1)]
			for k in range(len(B)):
				for l in range(len(D)):
					N[k + l] += B[k] @ D[l]
			
			if N[0] == Lo or N[-1] == Lo or M[0] == Lo or M[-1] == Lo:
				continue
			
			K = sum((N[_k] @ M[d - _k] for _k in range(d + 1)), Lo)
			
			if K != Li:
				try:
					Ki = K.inverse()
				except ArithmeticError:
					continue
				
				for m in range(d + 1):
					N[m] = Ki @ N[m]
			
			if __debug__:
				for m in range(d + 1):
					assert sum((N[_k] @ M[m - 1 - _k] for _k in range(m)), Lo) == Lo
				assert sum((N[_k] @ M[d - _k] for _k in range(d + 1)), Lo) == Li, str(sum((N[_k] @ M[d - _k] for _k in range(d + 1)), Lo))
			
			break
		
		return M, N


def fapkc_generate_io(d):
	Al = []
	Br = []
	for m in range(d - 1):
		Alm = random_singular(2)
		Brm = -sum((Br[_k] @ Al[m - 1 - _k] for _k in range(m)), Lo) - Alm
		Al.append(Alm)
		Br.append(Brm)
	
	assert len(Al) == len(Br) == d - 1
	
	A = []
	B = []
	A.append(random_singular(2))
	B.append(left_zero_divisor(A[0]))
	for m in range(d - 1):
		A.append(Al[m] @ A[0])
		B.append(B[0] @ Br[m])
	
	assert len(A) == len(B) == d
	
	A.append(None)
	B.append(None)
	
	while True:
		A[-1] = random_singular(2)
		B[-1] = random_singular(2)
		
		M = sum((B[_k] @ A[d - _k] for _k in range(d + 1)), Lo)
		try:
			Mi = M.inverse()
		except ArithmeticError:
			continue
		
		break
	
	assert len(A) == len(B) == d + 1
	
	for m in range(d + 1):
		B[m] = Mi @ B[m]
	
	if __debug__:
		for m in range(d + 1):
			assert sum((B[_k] @ A[m - 1 - _k] for _k in range(m)), Lo) == Lo
		assert sum((B[_k] @ A[d - _k] for _k in range(d + 1)), Lo) == Li, str(sum((B[_k] @ A[d - _k] for _k in range(d + 1)), Lo))
	
	return A, B


if __debug__:
	def test_i_io_basic():
		"Test FAPKC key generation in the most basic case, with delay 1, using algebraic formulas."
		
		As, Bs = fapkc_generate_io(1)
		
		assert Bs[0] @ As[0] == Lo
		assert Bs[0] @ As[1] + Bs[1] @ As[0] == Li
		
		i = [Rijndael.random(randrange) for _i in range(4)]
		o = [Rijndael.zero(), Rijndael.zero(), Rijndael.zero(), Rijndael.zero()]
		j = [Rijndael.zero(), Rijndael.zero(), Rijndael.zero(), Rijndael.zero()]
		
		t = 3
		
		o[t - 3] = As[0](i[t - 3])
		o[t - 2] = As[0](i[t - 2]) + As[1](i[t - 3])
		o[t - 1] = As[0](i[t - 1]) + As[1](i[t - 2])
		o[t - 0] = As[0](i[t - 0]) + As[1](i[t - 1])
		
		for t in (1, 2, 3):
			assert o[t] == As[0](i[t]) + As[1](i[t - 1])
		
		for t in (1, 2, 3):
			assert Bs[0](o[t]) == Bs[0](As[0](i[t])) + Bs[0](As[1](i[t - 1]))
			assert Bs[1](o[t]) == Bs[1](As[0](i[t])) + Bs[1](As[1](i[t - 1]))
		
		for t in (2, 3):
			assert Bs[1](o[t - 1]) == Bs[1](As[0](i[t - 1])) + Bs[1](As[1](i[t - 2]))
			
			assert Bs[0](o[t]) == (Bs[0] @ As[0])(i[t]) + (Bs[0] @ As[1])(i[t - 1])
			assert Bs[1](o[t - 1]) == (Bs[1] @ As[0])(i[t - 1]) + (Bs[1] @ As[1])(i[t - 2])
			
			assert Bs[0](o[t]) + Bs[1](o[t - 1]) == (Bs[0] @ As[0])(i[t]) + (Bs[0] @ As[1])(i[t - 1]) + (Bs[1] @ As[0])(i[t - 1]) + (Bs[1] @ As[1])(i[t - 2])
			assert Bs[0](o[t]) + Bs[1](o[t - 1]) == (Bs[0] @ As[1])(i[t - 1]) + (Bs[1] @ As[0])(i[t - 1]) + (Bs[1] @ As[1])(i[t - 2])
			assert Bs[0](o[t]) + Bs[1](o[t - 1]) == (Bs[0] @ As[1] + Bs[1] @ As[0])(i[t - 1]) + (Bs[1] @ As[1])(i[t - 2])
			assert Bs[0](o[t]) + Bs[1](o[t - 1]) == i[t - 1] + (Bs[1] @ As[1])(i[t - 2])
		
		j[t - 3] = Bs[0](o[t - 3])
		j[t - 2] = Bs[0](o[t - 2]) + Bs[1](o[t - 3]) - Bs[1](As[1](j[t - 3]))
		j[t - 1] = Bs[0](o[t - 1]) + Bs[1](o[t - 2]) - Bs[1](As[1](j[t - 2]))
		j[t - 0] = Bs[0](o[t - 0]) + Bs[1](o[t - 1]) - Bs[1](As[1](j[t - 1]))
		
		for t in (1, 2, 3):
			assert j[t] == i[t - 1]
	
	
	def test_i_io_1():
		As, Bs = fapkc_generate_io(1)
		
		A = Transducer(LinearCircuit({(0, 0):As[0], (0, 1):As[1]}))
		B = Transducer(LinearCircuit({(0, 0):Bs[0], (0, 1):Bs[1]}), LinearCircuit({(0, 0):Lo, (0, 1):-Bs[1] @ As[1]}))
		
		i = [Rijndael.random(randrange) for _i in range(100)]
		o = list(A(i))
		j = list(B(A(i)))
		
		for n in range(100):
			if n >= 1:
				assert j[n] == i[n - 1]
	
	
	def test_i_io_2():
		As, Bs = fapkc_generate_io(2)
		
		A = Transducer(LinearCircuit({(0, 0):As[0], (0, 1):As[1], (0, 2):As[2]}))
		B = Transducer(LinearCircuit({(0, 0):Bs[0], (0, 1):Bs[1], (0, 2):Bs[2]}), LinearCircuit({(0, 0):Lo, (0, 1):-Bs[2] @ As[1] - Bs[1] @ As[2], (0, 2):-Bs[2] @ As[2]}))
		
		i = [Rijndael.random(randrange) for _i in range(100)]
		o = list(A(i))
		j = list(B(A(i)))
		
		for n in range(100):
			if n >= 2:
				assert j[n] == i[n - 2]
	
	
	def test_i_i_basic():
		As, Bs = fapkc_generate_i(1)
		
		assert Bs[0] @ As[0] == Lo
		assert Bs[0] @ As[1] + Bs[1] @ As[0] == Li
		assert Bs[1] @ As[1] == Lo
		
		i = [Rijndael.random(randrange) for _i in range(4)]
		o = [Rijndael.zero(), Rijndael.zero(), Rijndael.zero(), Rijndael.zero()]
		j = [Rijndael.zero(), Rijndael.zero(), Rijndael.zero(), Rijndael.zero()]
		
		t = 3
		
		o[t - 3] = As[0](i[t - 3])
		o[t - 2] = As[0](i[t - 2]) + As[1](i[t - 3])
		o[t - 1] = As[0](i[t - 1]) + As[1](i[t - 2])
		o[t - 0] = As[0](i[t - 0]) + As[1](i[t - 1])
		
		for t in (1, 2, 3):
			assert o[t] == As[0](i[t]) + As[1](i[t - 1])
		
		for t in (1, 2, 3):
			assert Bs[0](o[t]) == Bs[0](As[0](i[t])) + Bs[0](As[1](i[t - 1]))
			assert Bs[1](o[t]) == Bs[1](As[0](i[t])) + Bs[1](As[1](i[t - 1]))
		
		for t in (2, 3):
			assert Bs[1](o[t - 1]) == Bs[1](As[0](i[t - 1])) + Bs[1](As[1](i[t - 2]))
			
			assert Bs[0](o[t]) == (Bs[0] @ As[0])(i[t]) + (Bs[0] @ As[1])(i[t - 1])
			assert Bs[1](o[t - 1]) == (Bs[1] @ As[0])(i[t - 1]) + (Bs[1] @ As[1])(i[t - 2])
			
			assert Bs[0](o[t]) + Bs[1](o[t - 1]) == (Bs[0] @ As[0])(i[t]) + (Bs[0] @ As[1])(i[t - 1]) + (Bs[1] @ As[0])(i[t - 1]) + (Bs[1] @ As[1])(i[t - 2])
			assert Bs[0](o[t]) + Bs[1](o[t - 1]) == (Bs[0] @ As[1])(i[t - 1]) + (Bs[1] @ As[0])(i[t - 1])
			assert Bs[0](o[t]) + Bs[1](o[t - 1]) == (Bs[0] @ As[1] + Bs[1] @ As[0])(i[t - 1])
			assert Bs[0](o[t]) + Bs[1](o[t - 1]) == i[t - 1]
		
		j[t - 3] = Bs[0](o[t - 3])
		j[t - 2] = Bs[0](o[t - 2]) + Bs[1](o[t - 3])
		j[t - 1] = Bs[0](o[t - 1]) + Bs[1](o[t - 2])
		j[t - 0] = Bs[0](o[t - 0]) + Bs[1](o[t - 1])
		
		for t in (1, 2, 3):
			assert j[t] == i[t - 1]


	def test_i_i_1():
		As, Bs = fapkc_generate_i(1)
		
		A = Transducer(LinearCircuit({(0, _k):As[_k] for _k in range(2)}))
		B = Transducer(LinearCircuit({(0, _k):Bs[_k] for _k in range(2)}))
		
		i = [Rijndael.random(randrange) for _i in range(100)]
		o = list(A(i))
		j = list(B(A(i)))
		
		for n in range(100):
			if n >= 1:
				assert j[n] == i[n - 1]


	def test_i_i_2():
		As, Bs = fapkc_generate_i(2)
		
		A = Transducer(LinearCircuit({(0, _k):As[_k] for _k in range(3)}))
		B = Transducer(LinearCircuit({(0, _k):Bs[_k] for _k in range(3)}))
		
		i = [Rijndael.random(randrange) for _i in range(100)]
		o = list(A(i))
		j = list(B(A(i)))
		
		for n in range(100):
			if n >= 2:
				assert j[n] == i[n - 2]


	def test_i_i(d):
		As, Bs = fapkc_generate_i(d)
		
		A = Transducer(LinearCircuit({(0, _k):As[_k] for _k in range(d + 1)}))
		B = Transducer(LinearCircuit({(0, _k):Bs[_k] for _k in range(d + 1)}))
		
		i = [Rijndael.random(randrange) for _i in range(100)]
		o = list(A(i))
		j = list(B(A(i)))
		
		for n in range(100):
			if n >= d:
				assert j[n] == i[n - d]


	def test_i_io(d):
		As, Bs = fapkc_generate_io(d)
		
		A = Transducer(LinearCircuit({(0, _k):As[_k] for _k in range(d + 1)}))
		B = Transducer(LinearCircuit({(0, _k):Bs[_k] for _k in range(d + 1)}), LinearCircuit({(0, _k):-sum((Bs[d - _l] @ As[_k + _l] for _l in range(d + 1 - _k)), Lo) if _k else Lo for _k in range(d + 1)}))
		
		i = [Rijndael.random(randrange) for _i in range(100)]
		o = list(A(i))
		j = list(B(A(i)))
		
		for n in range(100):
			if n >= d:
				assert j[n] == i[n - d]


def fapkc_generate_nl(d):
	m = {}
	n = {}
	
	c = [random_invertible() for _l in range(d)]
	
	for k in range(d):
		n[k] = Li
		for ll in range(k + 1):
			n[k] = n[k] @ c[ll]
		
		if k == 0:
			m[k, k] = Quadratic([n[k].inverse()] + [Lo] * 7)
			continue
		
		m[k, k] = Qo
		for l in range(k):
			m[l, k] = Quadratic.random(list, Linear, Rijndael, randrange)
			m[k, k] -= m[l, k]
		assert sum((m[_l, k] for _l in range(k + 1)), Qo) == Qo
		
		for l in range(k + 1):
			for ll in range(k - l):
				m[l, k] = c[k -ll] @ m[l, k]
		
		assert sum((n[_l] @ m[_l, k] for _l in range(k + 1)), Qo) == Qo
	
	for k in range(1, d):
		assert sum((n[_l] @ m[_l, k] for _l in range(k + 1)), Qo) == Qo
	
	return n, m



def linear_automata_pair_io(d):




'''






o = L(i) + P(i) + Q(o) + c
i = L**-1(o) - (L**-1 @ P)(i) - (L**-1 @ Q)(o) - L**-1(c)


p = K(j) + R(j) + S(p) + d
j = K**-1(p) - (K**-1 @ R)(j) - (K**-1 @ S)(p) - K**-1(d)


j = o
p  = ((K + R) @ (L + P))(i) + ((K + R) @ Q)(j) + S(p) + (K + R)(c) + d


j = f(o)
p = ((K + R) @ f @ (L + P))(i) + ((K + R) @ f @ Q)(j) + S(p) + ((K + R) @ f)(c) + d



o = L(i) + P(i) + Q(o) + c
p = f(o) + d
j = L**-1(p) - (L**-1 @ P)(j) - (L**-1 @ Q)(p) - L**-1(c)

j = ((L**-1 - L**-1 @ Q) @ f @ (L + P))(i) + ((L**-1 - L**-1 @ Q) @ f @ Q)(o) - (L**-1 @ P)(j) + ((L**-1 - L**-1 @ Q) @ f - L**-1)(c) + (L**-1 - (L**-1 @ Q))(d)


j = (L**-1 @ f @ (L + P))(i) - (L**-1 @ P)(j) + L**-1(f(c) - c + d)



k *= a * x + b






o = L(i) + P(i) + c
p = f(o) + e
j = K**-1(p) - (K**-1 @ R)(j) - (K**-1 @ S)(p) - K**-1(d)


j = (K**-1 @ f @ (L + P))(i) - (K**-1 @ R)(j) + K**-1(f(e) - c + d)




j = (K**-1 @ fg @ (L + P))(i) - (K**-1 @ R)(j) + K**-1(f(e) - c + d)



fg(i) = ((K**-1).sqrt() @ f @ LP_left)(i) * ((K**-1).sqrt() @ g @ LP_right)(i)



x**3 @ x**3 = x**3**3 = x**9


x**2 * x




A = ((K**-1).sqrt() @ f @ LP_left)(i)  + (J**-1).sqrt()(A)
B = ((K**-1).sqrt() @ g @ LP_right)(i) + (J**-1).sqrt()(B)
C = (K**-1 @ R)(j)                     + J**-1(C)
D = K**-1(f(e) - c + d)                + J**-1(D)

j = A * B + C + D











(K @ Q)(j) = (K @ Q @ K**-1)(p) - (K @ Q @ K**-1 @ R)(j) - (K @ Q @ K**-1 @ S)(p)

p = (K @ L)(i) + (K @ P)(i) + (K @ Q)(j) + (R @ L)(i) + (R @ P)(i) + (R @ Q)(j) + S(p)



p = (K @ L)(i) + (K @ P)(i) + (R @ L)(i)         + (R @ P)(i)             + S(p)
p = (K @ L)(i) + (K @ P)(i) + (K @ Q @ K**-1)(p) - (K @ Q @ K**-1 @ S)(p) + S(p)




o = L(i) + P(i) + c
p = K(o) + S(p) + d

p = (K @ L)(i) + (K @ P)(i) + S(p) + K(c) + d

i = L**-1(o) - (L**-1 @ P)(i) - L**-1(c)





o = L(i) + P(i) + c
p = f(o) + d = f(L(i) + P(i) + c) + d = (f @ L)(i) + (f @ P)(i) + f(c) + d
j = L**-1(p) - (L**-1 @ P)(j) + e = L**-1((f @ L)(i) + (f @ P)(i) + f(c) + d) - (L**-1 @ P)(j) + e = (L**-1 @ f @ L)(i) + (L**-1 @ f @ P)(i) + (L**-1 @ f)(c) + L**-1(d) - (L**-1 @ P)(j) + e




o = L(i) + P(i) + c
p[t] = o[t] * p[t - 1]
j = L**-1(p[t]) - (L**-1 @ P)(j[t - 1:]) + e


o = L(i) + P(i) + c
p[t] = o[t] * p[t - 1] = L(i) * p[t - 1] + P(i) * p[t - 1] + c * p[t - 1]
j = L**-1(p[t]) - (L**-1 @ P)(j[t - 1:]) + e



p[t] = L(i) * p[t - d - 1] + P(i) * p[t - d - 1] + c * p[t - d - 1]

p[t - d - 1] = L(j) + (L @ L**-1 @ P)(j[t - 2:]) - L(e)


L(i[t - d:]) * (L(j) + (L @ L**-1 @ P)(j[t - 2:]) - L(e)) +
P(i[t - d:]) * (L(j) + (L @ L**-1 @ P)(j[t - 2:]) - L(e)) +
c * (L(j) + (L @ L**-1 @ P)(j[t - 2:]) - L(e))



P(i[t - d:]) * (L @ L**-1 @ P)(j[t - 2:])


x**3 * y**3



o = L(i) + P(i) + c
p = f(o) + d
j = L**-1(p) - (L**-1 @ P)(j) + e




a * b + c


a, b, 0, c, 1

a*b, 0, 0, c

a*b, 0, c
a*b, c
a*b + c


A, B, X, C, 0
A+B, B+X, C+X, C
a*b, b*x, c*x, c




  x,   x,    x, 1, 1, 1
    x*x, x*x, x, 1, 1
      x**4, x**3, x, 1





o = L(i) + P(i)
p = f(o) * g(o) = f(L(i) + P(i)) * g(L(i) + P(i))
j = L**-1(p) - (L**-1 @ P)(j) = L**-1(f(L(i) + P(i)) * g(L(i) + P(i))) - (L**-1 @ P)(j)



o = L(i)
p = o * p
j = M**-1(p)
M(j) = p

p = L(i) * M(j)
j = M**-1 @ (L * M)(i, j)


o = M(i)
p = o + p
j = N**-1(p)
N(j) = p

p = M(i) + N(j)
j = N**-1 @ (M + N)(i, j)



o = L(i) + P(i)
p = f(o) + g(o) = f(L(i) + P(i)) + g(L(i) + P(i))
j = L**-1(p) - (L**-1 @ P)(j) = L**-1(f(L(i) + P(i)) + g(L(i) + P(i))) - (L**-1 @ P)(j)




exp(i)
log(o)



1, x, x**2, x**3, x**4, ...

a, b, c, d



a, x, b, x, c, x

o[t] = c[t - 1] * i[t]
c[t] = c[t - 2] * i[t]

a, x,   a*b, x*x,   a*b*c, x*x*x
a, x*a, b*x, x*a*b, c*x**2



exp(log(a) + log(b))

255 * 255 = 




o[t] = i[t] + Q(i[t - 1])
p = M(o)
q[t] = f(p[t]) * g(p[t - 1])

q[t] = f(M(o[t])) * g(M(o[t - 1])) = (f(M(i[t])) + f(M(Q(i[t])))) * (g(M(i[t - 1])) + g(M(Q(i[t - 1]))))

r = N(q) = N(f(M(i) + M(Q(i))))
j = r + Q(j) = N(f(M(i) + M(Q(i)))) + Q(j)
'''



'''

linearA, linearB = fapkc_generate_linear_io(8)
quadraticA, quadraticB = fapkc_generate_quadratic(8)


public_key = quadraticA @ linearA


cipher = public_key(iv(8) + text)
text = linearB(quadraticB(cipher + padding(8)))









'''



if __name__ == '__main__':	
	_0 = Rijndael.zero()
	_1 = Rijndael.one()
	
	print(Rijndael.logarithm)
	print(Rijndael.exponent)
	
	Qo = Quadratic.zero(list, Linear, Rijndael)
	
	Lo = Linear.zero(list, Rijndael)
	Li = Linear.one(list, Rijndael)

	X = sum(rijndael_bits[:4], Lo)
	Y = sum(rijndael_bits[4:], Lo)

	print(function_image(X) & function_image(Y))
	quit()

	
	R = random_invertible()
	Ri = R.inverse()
	
	d = 4
	A, B = fapkc_generate_i(d)
	
	S = {}
	for k, l in product(range(1, 5), repeat=2):
		S[k, l] = Quadratic.random(list, Linear, Rijndael, randrange)
	
	f = random_singular(16)
	g = random_singular(16)
	
	tn = 40
	i = [Rijndael.random(randrange) for _n in range(tn)]
	il = [None] * tn
	o = [None] * tn
	jl = [None] * tn
	j = [None] * tn
	
	for t in range(tn):
		il[t] = Rijndael.sum(A[_o](i[t - _o]) for _o in range(d + 1) if (t - _o >= 0))
		o[t] = Ri(il[t]) - Rijndael.sum((Ri @ S[_k, _l])(o[t - _k], o[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0))
	
	for t in range(tn):
		jl[t] = R(o[t]) + Rijndael.sum(S[_k, _l](o[t - _k], o[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0))
		j[t] = Rijndael.sum(B[_o](jl[t - _o]) for _o in range(d + 1) if (t - _o >= 0))
	
	#print(*i)
	#print(*il)
	#print(*o)
	#print(*jl)
	#print(*j)
	
	assert j[d:] == i[:-d]
	#quit()
	
	i = [Rijndael.random(randrange) for _n in range(tn)]
	il = [None] * tn
	p = [None] * tn
	pl = [None] * tn
	u = [None] * tn
	v = [None] * tn
	ql = [None] * tn
	q = [None] * tn
	jl = [None] * tn
	j = [None] * tn
	
	for t in range(tn):
		il[t] = Rijndael.sum(A[_o](i[t - _o]) for _o in range(d + 1) if (t - _o >= 0))
		p[t] = Ri(il[t]) - Rijndael.sum((Ri @ S[_k, _l])(p[t - _k], p[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0))
	
	#o = NN(i)
	#NN*-1(o) = i
	
	#A * x * y + B * x**2 * y + C * x * y**2 + D * x**2 * y**2
	
	#o = Q(i)
	#(L @ R)(o) = (L @ Q)(i) * (R @ Q)(i)
	
	for t in range(tn):
		#decrypt_linear(i)
		#decrypt_quadratic(i)
		
		#encrypt_quadratic(i)
		#encrypt_linear(i)
		
		
		pl[t] = R(p[t]) + Rijndael.sum(S[_k, _l](p[t - _k], p[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0))
		u[t] = Rijndael.sum(B[_o](pl[t - _o]) for _o in range(d + 1) if (t - _o >= 0))
		
		v[t] = f(u[t])
		
		ql[t] = Rijndael.sum(A[_o](v[t - _o]) for _o in range(d + 1) if (t - _o >= 0))
		q[t] = Ri(ql[t]) - Rijndael.sum((Ri @ S[_k, _l])(q[t - _k], q[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0))
	
	for t in range(tn):
		jl[t] = R(q[t]) + Rijndael.sum(S[_k, _l](q[t - _k], q[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0))
		j[t] = Rijndael.sum(B[_o](jl[t - _o]) for _o in range(d + 1) if (t - _o >= 0))
	
	k = [f(_i) for _i in i]
	
	print("i :", *i)
	print("il:", *il)
	print("p :", *p)
	print("pl:", *pl)
	print("u: ", *u[d:])
	print("v: ", *v[d:])
	#print("ql:", *ql[d:])
	print("q :", *q[2*d:])
	#print("jl:", *jl[2*d:])
	print("j :", *j[2*d:])
	print("k: ", *k)
	
	assert i[:-d] == u[d:]
	assert k[:-d] == v[d:]
	assert k[:-2*d] == j[2*d:]
	
	quit()
	
	Qr = random_singular_nl(8)
	Ql = left_zero_divisor_nl(Qr)
	
	assert Qr
	assert Ql
	assert Ql @ Qr == Qo
	
	quit()
	
	for i in range(Rijndael.field_power):
		print([str((Qa2 @ Q0).quadratic_coefficient((i - j) % Rijndael.field_power, j)) for j in range(Rijndael.field_power)])
	print()
	
	quit()
	
		
	B = random_singular(4)
	A = left_zero_divisor(B)
	C = random_invertible()	
	D = random_invertible()
	
	for x in Rijndael.domain():
		assert C.pow_base(1)(x) == (C * C)(x, x) == C(x) * C(x)
		assert (B * D)(x, x) == B(x) * D(x)
	
	assert (C * C) @ (B, D) == (C @ B) * (C @ D)
	print(C @ (B * B)) # == (C @ B) * (C @ B))


	
	assert A @ B == Lo
	assert (B @ A) @ (B @ A) == Lo
	
	AC = A * C
	BC = B * C
	
	assert (A @ B) * (A @ C) == Qo
	assert AC @ (B, D) == Qo
	
	
	
	quit()
	fapkc_generate_nl(4)
	
	test_i_io_basic()
	test_i_i_basic()
	
	test_i_io_1()
	test_i_io_2()
	
	test_i_i_1()
	test_i_i_2()
	
	for d in range(1, 20):
		print(d)
		test_i_io(d)
		test_i_i(d)




	
	quit()


	
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




'''
w[t] = (f @ Ri)(p[t]) - Rijndael.sum((f @ Ri @ S[_k, _l])(p[t - _k], p[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0)) - Rijndael.sum((f @ T[_k] @ f.pseudoinverse())(w[t - _k]) for _k in T.keys() if (t - _k >= 0))
w[t - 1] = (f @ Ri)(p[t - 1]) - Rijndael.sum((f @ Ri @ S[_k, _l])(p[t - _k - 1], p[t - _l - 1]) for _k, _l in S.keys() if (t - _k >= 1) and (t - _l >= 1)) - Rijndael.sum((f @ T[_k] @ f.pseudoinverse())(w[t - _k - 1]) for _k in T.keys() if (t - _k >= 1))

w[t] = (f @ Ri)(p[t])
 - Rijndael.sum((f @ Ri @ S[_k, _l])(p[t - _k], p[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0))
 - (f @ T[1] @ f.pseudoinverse())(w[t - 1])
 - Rijndael.sum((f @ T[_k] @ f.pseudoinverse())(w[t - _k]) for _k in T.keys() if (t - _k >= 2))

w[t] = (f @ Ri)(p[t])
 - Rijndael.sum((f @ Ri @ S[_k, _l])(p[t - _k], p[t - _l]) for _k, _l in S.keys() if (t - _k >= 0) and (t - _l >= 0))
 
 - (f @ T[1] @ Ri)(p[t - 1])
 + Rijndael.sum((f @ T[1] @ Ri @ S[_k, _l])(p[t - _k - 1], p[t - _l - 1]) for _k, _l in S.keys() if (t - _k >= 1) and (t - _l >= 1))


 + Rijndael.sum((f @ T[1] @ T[_k] @ f.pseudoinverse())(w[t - _k - 1]) for _k in T.keys() if (t - _k >= 1))

 - Rijndael.sum((f @ T[_k] @ f.pseudoinverse())(w[t - _k]) for _k in T.keys() if (t - _k >= 2))

(T[1] @ T[1])(w[t - 2]) + (T[1] @ T[2])(w[t - 3])
T[2](w[t - 2]) + T[3](w[t - 3]) + ...
'''




#Rijndael.sum((f @ T[_k])(w[t - _k]) for _k in T.keys() if (t - _k >= 0))


