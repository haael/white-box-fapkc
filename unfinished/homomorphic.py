#!/usr/bin/python3


from fields import Binary
from random import randrange
from machines import *
from linear import *
from utils import subscript


if __name__ == '__main__':
	def random_stream(n, size, Array, Field, randbelow):
		while n > 0:
			n -= 1
			yield Vector.random(size, Array, Field, randbelow)
	
	print()
	d = Automaton.random_quadratic_quadratic(8, 8, 8, dict, list, Vector, QuadraticCircuit, Quadratic, Linear, Binary, randrange)
	for n, x in enumerate(d(random_stream(256, 8, list, Binary, randrange))):
		print(n, x)
	
	def add(v):
		a = int(v[0])
		b = int(v[1])
		
		f = F((a + b) % F.field_size)
		g = F((a + b) // F.field_size)
		
		return v.__class__([f, g])
	
	def circuit_fn_2(fn):
		m, n
		
		for xn in product(range(F.field_size), repeat=m):
			point_polynomial[xn[i]]
	
	variable = [sympy.Poly(sympy.Symbol(f'x{subscript(_n)}')) for _n in range(len(args))]
	r = sympy.Poly(0)
	s = sympy.Poly(1)
	for n, arg in enumerate(args):
		s *= point_polynomial[arg](variable[n])
	r += result * s


	x * y * z
	result = s[-1] * z[-1]
	s[0] = 	x[0] * y[0]
	
	x**2 * y + x * z + 1
	s[0] = x**2
