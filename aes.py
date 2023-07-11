#!/usr/bin/python3


__all__ = 'Rijndael', 'RijndaelPolynomial', 'point_polynomial', 'polynomial_fn', 'aes_forward_sbox', 'aes_inverse_sbox', 'increment'


from pickle import load, dump
from pathlib import Path
from fields import Galois, Polynomial


Rijndael = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])

assert Rijndael(0x53) * Rijndael(0xca) == Rijndael(0x01)

class RijndaelPolynomial(Polynomial):
	Field = Rijndael


try:
	with Path('point_polynomial.pickle').open('rb') as fd:
		point_polynomial = load(fd)
except (IOError, EOFError):
	def point_polynomials():
		pp = []
		x = RijndaelPolynomial(1, 0)
		for n in range(Rijndael.field_size):
			r = RijndaelPolynomial(1)
			for m in range(Rijndael.field_size):
				if m == n: continue
				r *= (x - RijndaelPolynomial(m))
			r *= RijndaelPolynomial(r(Rijndael(n)) ** -1)
			pp.append(r)
			print(n)
		return pp
	
	point_polynomial = point_polynomials()
	
	del point_polynomials
	
	with Path('point_polynomial.pickle').open('wb') as fd:
		dump(point_polynomial, fd)


def polynomial_fn(f):
	p = RijndaelPolynomial()
	for n in range(Rijndael.field_size):
		p += point_polynomial[n] * RijndaelPolynomial(f(Rijndael(n)))
	return p


@polynomial_fn
def aes_forward_sbox(n):
	if n:
		b = int(n ** -1)
	else:
		b = 0
	
	r = Rijndael(0x63)
	for m in [0, 1, 2, 3, 4]:
		r += Rijndael(((b << m) & 0xff) | (b >> (8 - m)))
	return r


@polynomial_fn
def aes_inverse_sbox(n):
	b = int(n)
	r = Rijndael(0x5)
	for m in [1, 3, 6]:
		r += Rijndael(((b << m) & 0xff) | (b >> (8 - m)))
	
	if r:
		return r ** -1
	else:
		return Rijndael(0)


@polynomial_fn
def increment(n):
	return Rijndael((int(n) + 1) % 0x100)








