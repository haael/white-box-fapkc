#!/usr/bin/python3


"Implementations of some composable operations over finite fields: vectors, matrices, quasilinear functions and quasiquadratic functions."


__all__ = 'Linear', 'Quadratic', 'Vector', 'Matrix'


from itertools import zip_longest, product, chain, permutations
from math import sqrt, ceil
from collections import defaultdict

from utils import superscript, cached, array_fallback, table_fallback


class Linear:
	"Quasilinear function of single argument. `F(x + y) = F(x) + F(y); F(0) = 0`. The name 'linear' comes from analogy to matrices."
	
	@property
	@cached
	def Field(self):
		return self.__f[0].Field
	
	@classmethod
	@property
	def Linear(cls):
		return cls
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__f.__class__)
	
	def zero_element(self):
		return self.Field.zero()
	
	def one_element(self):
		return self.Field.one()
	
	@classmethod
	def zero(cls, Array, Field):
		nArray = array_fallback(Array)		
		return cls(nArray((Field.zero() for _n in range(Field.field_power)), [None], [Field]))
	
	@classmethod
	def one(cls, Array, Field):
		nArray = array_fallback(Array)		
		return cls(nArray(chain([Field.one()], (Field.zero() for _n in range(Field.field_power - 1))), [None], [Field]))
	
	ident = one
	
	@classmethod
	def factor(cls, value, Array):
		nArray = array_fallback(Array)		
		Field = value.__class__
		return cls(nArray(chain([value], (Field.zero() for _n in range(Field.field_power - 1))), [None], [Field]))
	
	@classmethod
	def random(cls, Array, Field, randbelow):
		nArray = array_fallback(Array)		
		return cls(nArray((Field.random(randbelow) for n in range(Field.field_power)), [None], [Field]))
	
	@classmethod
	def random_nonzero(cls, Array, Field, randbelow):
		nArray = array_fallback(Array)
		
		f = []
		nonzero = False
		for n in range(Field.field_power - 1):
			v = Field.random(randbelow)
			if v:
				nonzero = True
			f.append(v)
		
		if nonzero:
			f.append(Field.random(randbelow))
		else:
			f.append(Field.random_nonzero(randbelow))
		
		return cls(nArray(f, [None], [Field]))
	
	'''
	@classmethod
	def random_factor(cls, Array, Field, randbelow):
		return cls.factor(Field.random(randbelow), Array)
	
	@classmethod
	def random_factor_nonzero(cls, Array, Field, randbelow):
		return cls.factor(Field.random_nonzero(randbelow), Array)
	'''
	
	def __init__(self, coefficients):
		"f[0] * x + f[1] * x**p + f[2] * x**(p ** 2) + ... + f[k] * x**(p ** k)"
		
		try:
			self.__f = coefficients.__f
		except (AttributeError, TypeError):
			self.__f = coefficients
		
		if not len(self.__f) == self.Field.field_power:
			raise ValueError(f"Linear function over {self.Field.__name__} needs {self.Field.field_power} parameters. (Got {len(self.__f)})")
	
	def __getnewargs__(self):
		return (self.__f,)
	
	def serialize(self):
		try:
			return self.__f.serialize()
		except AttributeError:
			return map(int, self.__f)
	
	@classmethod
	def deserialize(cls, Array, Field, data):
		nArray = array_fallback(Array)		
		return cls(nArray((Field.deserialize(data) for n in range(Field.field_power)), [None], [Field]))
	
	def linear_coefficient(self, i):
		return self.__f[i]
	
	def __str__(self):
		return " + ".join(f"{self.__f[_n]}·x{superscript(self.Field.field_base ** _n)}" for _n in range(self.Field.field_power))
	
	def __repr__(self):
		return self.__class__.__name__ + '(' + ", ".join([repr(_f) for _f in self.__f]) + ')'
	
	def __call__(self, x):
		Field = self.Field
		p = Field.field_base
		n = Field.field_power
		f = self.__f
		return Field.sum(f[_n] * x**(p ** _n) for _n in range(n))
	
	def inverse(self, Table=dict):
		size = self.Field.field_power
		mat = Matrix.zero(size, size, Table, self.Array, self.Field)
		
		for m, n in product(range(size), range(size)):
			mat[n, m] = self.__f[(m - n) % size]**(self.Field.field_base ** n)
		w = mat.determinant()
		
		result = []
		for n in range(size):
			for m in range(size):
				mat[n, m] = self.Field.one() if m == 0 else self.Field.zero()
			
			result.append(mat.determinant() / w)
			
			for m in range(size):
				mat[n, m] = self.__f[(m - n) % size]**(self.Field.field_base ** n)
		
		return self.__class__(self.Array(result, [size], [self.Field]))
	
	def __add__(self, other):
		try:
			return self.__class__(self.Array((_a + _b for (_a, _b) in zip(self.__f, other.__f)), [None], [self.Field]))
		except AttributeError as error:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__(self.Array((_a - _b for (_a, _b) in zip(self.__f, other.__f)), [None], [self.Field]))
		except AttributeError:
			return NotImplemented
	
	def __neg__(self):
		return self.__class__(self.Array((-_a for _a in self.__f), [None], [self.Field]))
	
	def __mul__(self, other):
		try:
			if other.Field != self.Field:
				return NotImplemented
			if not (hasattr(other, 'field_power') and hasattr(other, 'field_base')):
				return NotImplemented
		except AttributeError:
			return NotImplemented
		else:
			return self.__class__(self.Array((_a * other for _a in self.__f), [None], [self.Field]))
	
	def __rmul__(self, other):
		try:
			if other.Field != self.Field:
				return NotImplemented
			if not (hasattr(other, 'field_power') and hasattr(other, 'field_base')):
				return NotImplemented
		except AttributeError:
			return NotImplemented
		else:
			return self.__class__(self.Array((other * _a for _a in self.__f), [None], [self.Field]))
	
	def __matmul__(self, other):
		try:
			f = [self.Field.zero()] * self.Field.field_power
			
			for m in range(self.Field.field_power):
				for n in range(other.Field.field_power):
					f[(m + n) % self.Field.field_power] += self.__f[m] * other.__f[n]**(self.Field.field_base ** m)
			
			return self.__class__(self.Array(f, [None], [self.Field]))
		
		except AttributeError:
			return NotImplemented
	
	def __eq__(self, other):
		try:
			return self.__f == other.__f
		except AttributeError:
			return NotImplemented


class Quadratic:
	"Class of functions of 2 variables, containing the product `f(x, y) = x * y` and closed over quasilinear transformations."
	
	@property
	@cached
	def Field(self):
		return self.__f[0].Field
	
	@property
	@cached
	def Linear(self):
		return self.__f[0].Linear
	
	@classmethod
	@property
	def Quadratic(cls):
		return cls
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__f.__class__)
	
	@classmethod
	def zero(cls, Array, Linear, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Linear.zero(Array, Field) for _i in range(Field.field_power)), [Field.field_power, None], [Linear, Field]))
	
	@classmethod
	def one(cls, Array, Linear, Field):
		nArray = array_fallback(Array)
		return cls(nArray((chain([Linear.one(Array, Field)], (Linear.zero(Array, Field) for _i in range(Field.field_power)))), [Field.field_power, None], [Linear, Field]))
	
	@classmethod
	def random(cls, Array, Linear, Field, randbelow):
		nArray = array_fallback(Array)
		return cls(nArray((Linear.random(Array, Field, randbelow) for _i in range(Field.field_power)), [Field.field_power, None], [Linear, Field]))
	
	# TODO: ident, random_nonzero
	
	def __init__(self, coefficients):
		"f[0](x * y) + f[1](x * y**p) + f[2](x * y ** (p ** 2)) + f[3](x * y ** (p ** 3)) + ... + f[k](x * y ** (p ** k))"
		
		try:
			self.__f = coefficients.__f
			return
		except AttributeError:
			pass
		
		self.__f = coefficients
		
		if not len(self.__f) == self.Field.field_power:
			raise ValueError(f"Linear function over {self.Field.__name__} needs {self.Field.field_power} parameters. (Got {len(self.__f)}.)")
	
	def __getnewargs__(self):
		return (self.__f,)
	
	def serialize(self):
		try:
			return self.__f.serialize()
		except AttributeError:
			return chain.from_iterable(_v.serialize() for _v in self.__f)
	
	@classmethod
	def deserialize(cls, Array, Linear, Field, data):
		nArray = array_fallback(Array)
		return cls(nArray((Linear.deserialize(Array, Field, data) for _i in range(Field.field_power)), [Field.field_power, None], [Linear, Field]))
	
	def quadratic_coefficient(self, i, j):
		return self.__f[i].linear_coefficient(j)
	
	def __call__(self, x, y):
		Field = self.Field
		p = Field.field_base
		n = Field.field_power
		f = self.__f
		#print("calling:", type(f[0]).__name__, f[0].__call__)
		return Field.sum(f[_k](x * y**(p ** _k)) for _k in range(n))
	
	def __add__(self, other):
		try:
			return self.__class__(self.Array((_a + _b for (_a, _b) in zip(self.__f, other.__f)), [self.Field.field_power, None], [self.Linear, self.Field]))
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__(self.Array((_a - _b for (_a, _b) in zip(self.__f, other.__f)), [self.Field.field_power, None], [self.Linear, self.Field]))
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		return self.__class__(self.Array((_a * other for _a in self.__f), [self.Field.field_power, None], [self.Linear, self.Field]))
	
	def __rmul__(self, other):
		return self.__class__(self.Array((other * _a for _a in self.__f), [self.Field.field_power, None], [self.Linear, self.Field]))
	
	def __matmul__(self, other):
		"Composition of quadratic operation with 2 quasilinear operations. `(q @ (l1, l2))(x, y) = q(l1(x), l2(y))`"
		
		try:
			b, c = other
		except ValueError:
			return NotImplemented
		
		m = self.Field.field_power
		p = self.Field.field_base
		
		d = defaultdict(lambda: self.Field.zero())
		for (i, j, k, l) in product(range(m), repeat=4):
			d[(i + l) % m, (j + k - i) % m] += self.quadratic_coefficient(k, l) * b.linear_coefficient(i)**(p**l) * c.linear_coefficient(j)**(p ** ((k + l) % m))
		
		f = []
		for j in range(m):
			f.append(b.__class__(b.Array((d[i, j] for i in range(m)), [None], [self.Field])))
		
		return self.__class__(self.Array(f, [m, None], [self.Linear, self.Field]))
	
	def __rmatmul__(self, other):
		"Composition of quasilinear operation with quadratic operation. `(l @ q)(x, y) = l(q(x, y))`"
		
		return self.__class__(self.Array((other @ _f for _f in self.__f), [self.Field.field_power, None], [self.Linear, self.Field]))
	
	def __eq__(self, other):
		try:
			return self.__f == other.__f
		except AttributeError:
			return NotImplemented


class Vector:
	@property
	@cached
	def Field(self):
		return self[0].Field
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__values.__class__)
	
	@cached
	def zero_element(self):
		return self.Field.zero()
	
	@cached
	def one_element(self):
		return self.Field.one()
	
	@classmethod
	def random(cls, length, Array, Field, randbelow):
		nArray = array_fallback(Array)
		return cls(nArray((Field.random(randbelow) for _n in range(length)), [None], [Field]))
	
	@classmethod
	def random_nonzero(cls, length, Array, Field, randbelow):
		nArray = array_fallback(Array)
		
		values = []
		nonzero = False
		for n in range(length):
			if not nonzero and n == length - 1:
				f = Field.random_nonzero(randbelow)
			else:
				f = Field.random(randbelow)
			
			if f:
				nonzero = True
			
			values.append(f)
		
		return cls(nArray(values, [None], [Field]))
	
	@classmethod
	def zero(cls, length, Array, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Field.zero() for _n in range(length)), [None], [Field]))
	
	def __init__(self, values):
		try:
			self.__values = values.__values
			self.vector_length = values.vector_length
		except AttributeError:
			pass
		else:
			return
		
		self.__values = values
		self.vector_length = len(values)
	
	def __getnewargs__(self):
		return self.__values,
	
	def serialize(self):
		try:
			return self.__values.serialize()
		except AttributeError:
			return self.__values
	
	@classmethod
	def deserialize(cls, length, Array, Field, data):
		nArray = array_fallback(Array)
		return cls(nArray((Field.deserialize(data) for _n in range(length)), [None], [Field]))
	
	def __repr__(self):
		return f'{self.__class__.__name__}({{{ ", ".join(str(_n) + ": " + str(self.__values[_n]) for _n in self.keys()) }}})'
	
	def __str__(self):
		return "Vector[" + ", ".join([str(_v) for _v in self.__values]) + "]"
	
	def __len__(self):
		return self.vector_length
	
	def keys(self):
		yield from range(len(self))
	
	def values(self):
		yield from self.__values
	
	def items(self):
		yield from enumerate(self.__values)
	
	def __getitem__(self, index):
		if index is Ellipsis:
			return self.__class__(self.Array(iter(self), [None], [self.Field]))
		elif hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step'):
			return self.__class__(self.__values[index])
		else:
			return self.__values[index]
	
	def __setitem__(self, index, value):
		if index is Ellipsis or (hasattr(index, 'start') and hasattr(index, 'stop') and hasattr(index, 'step')):
			if hasattr(value, '_Vector__values'):
				self.__values[index] = value.__values
			else:
				self.__values[index] = value
		else:
			self.__values[index] = value
	
	def __eq__(self, other):
		try:
			return len(self) == len(other) and all(self[_n] == other[_n] for _n in self.keys())
		except (TypeError, AttributeError):
			return NotImplemented
	
	def __or__(self, other):
		return self.__class__(self.Array(chain(self, other), [None], [self.Field]))
	
	def __ror__(self, other):
		return self.__class__(self.Array(chain(other, self), [None], [self.Field]))
	
	def __add__(self, other):
		if hasattr(other, 'vector_length'):
			if self.vector_length != other.vector_length:
				raise ValueError(f"Vector lengths don't match ({self.vector_length} vs. {other.vector_length}).")
			return self.__class__(self.Array((self[_n] + other[_n] for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented
	
	def __sub__(self, other):
		if hasattr(other, 'vector_length'):
			if self.vector_length != other.vector_length:
				raise ValueError(f"Vector lengths don't match ({self.vector_length} vs. {other.vector_length}).")
			return self.__class__(self.Array((self[_n] - other[_n] for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented
	
	def __neg__(self):
		return self.__class__(self.Array((-self[_n] for _n in self.keys()), [None], [self.Field]))
	
	def __mul__(self, other):
		try:
			return self.__class__(self.Array((self[_n] * other for _n in self.keys()), [None], [self.Field]))
		except TypeError:
			return NotImplemented
	
	def __rmul__(self, other):
		try:
			return self.__class__(self.Array((other * self[_n] for _n in self.keys()), [None], [self.Field]))
		except TypeError:
			return NotImplemented
	
	def __matmul__(self, other):
		if hasattr(other, 'vector_length'):
			if self.vector_length != other.vector_length:
				raise ValueError("Vector lengths don't match.")
			return self.Field.sum(self[_n] @ other[_n] for _n in self.keys())
		elif hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__(self.Array((self[_n] @ other for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented
	
	def __rmatmul__(self, other):
		if hasattr(other, 'vector_length'):
			if self.vector_length != other.vector_length:
				raise ValueError("Vector lengths don't match.")
			return self.Field.sum(other[_n] @ self[_n] for _n in self.keys())
		elif hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying vector by a scalar from a different field.")
			return self.__class__(self.Array((other @ self[_n] for _n in self.keys()), [None], [self.Field]))
		else:
			return NotImplemented


class Matrix:
	@property
	@cached
	def Field(self):
		return self[0, 0].Field
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__values.__class__)
	
	@property
	@cached
	def Table(self):
		return table_fallback(self.__values.__class__)
	
	@cached
	def zero_element(self):
		return self.Field.zero()
	
	@cached
	def one_element(self):
		return self.Field.one()
	
	@classmethod
	def random(cls, height, width, Table, Array, Field, randbelow):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), Field.random(randbelow)) for (_m, _n) in product(range(height), range(width))), [height, width], [None], [Field], Array=Array))
	
	@classmethod
	def zero(cls, height, width, Table, Array, Field):
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), Field.zero()) for (_m, _n) in product(range(height), range(width))), [height, width], [None], [Field], Array=Array))
	
	@classmethod
	def one(cls, height, width, Table, Array, Field):
		if height != width:
			raise ValueError("Unit matrix height must be equal to width.")
		nTable = table_fallback(Table)
		return cls(nTable((((_m, _n), (Field.one() if _m == _n else Field.zero())) for (_m, _n) in product(range(height), range(width))), [height, width], [None], [Field], Array=Array))
	
	ident = one
	
	def __init__(self, values):		
		try:
			self.__values = values.__values
			self.matrix_height = values.matrix_height
			self.matrix_width = values.matrix_width
		except AttributeError:
			pass
		else:
			return
		
		width = 0
		height = 0
		for m, n in values.keys():
			if m >= height:
				height = m + 1
			if n >= width:
				width = n + 1
		
		self.__values = values
		self.matrix_height = height
		self.matrix_width = width
	
	def __bool__(self):
		return any(self.values())
	
	def __str__(self):
		return 'Matrix[' + ', '.join('[' + ', '.join(str(self[_m, _n]) for _n in range(self.matrix_width)) + ']' for _m in range(self.matrix_height)) + ']'
	
	def keys(self):
		yield from product(range(self.matrix_height), range(self.matrix_width))
	
	def values(self):
		yield from self.__values.values()
	
	def items(self):
		yield from self.__values.items()
	
	def __getitem__(self, index):
		try:
			m, n = index
		except ValueError:
			raise IndexError
		return self.__values[m, n]
	
	def __setitem__(self, index, value):
		try:
			m, n = index
		except ValueError:
			raise IndexError
		self.__values[m, n] = value
	
	def __eq__(self, other):
		try:
			return self.matrix_width == other.matrix_width and self.matrix_height == other.matrix_height and all(self[_m, _n] == other[_m, _n] for (_m, _n) in self.keys())
		except (IndexError, AttributeError):
			return NotImplemented
	
	def __add__(self, other):
		if hasattr(other, 'matrix_width') and hasattr(other, 'matrix_height'):
			if not (self.matrix_width == other.matrix_width and self.matrix_height == other.matrix_height):
				raise ValueError("Matrix dimensions don't match.")
			return self.__class__(self.Table((((_m, _n), self[_m, _n] + other[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		else:
			return NotImplemented
	
	def __sub__(self, other):
		if hasattr(other, 'matrix_width') and hasattr(other, 'matrix_height'):
			if not (self.matrix_width == other.matrix_width and self.matrix_height == other.matrix_height):
				raise ValueError("Matrix dimensions don't match.")
			return self.__class__(self.Table((((_m, _n), self[_m, _n] - other[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		else:
			return NotImplemented
	
	def __matmul__(self, other):
		if hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying matrix by a scalar from a different field.")
			return self.__class__(self.Table((((_m, _n), self[_m, _n] @ other) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		elif hasattr(other, 'vector_length'):
			if self.matrix_width != other.vector_length:
				raise ValueError("Matrix width does not equal vector length.")
			return other.__class__(other.Array((self.Field.sum(self[_m, _n] @ other[_n] for _n in range(self.matrix_width)) for _m in range(self.matrix_height)), [None], [self.Field]))
		elif hasattr(other, 'matrix_width') and hasattr(other, 'matrix_height'):
			if self.matrix_width != other.matrix_height:
				raise ValueError("Left matrix height does not equal right matrix width.")
			return self.__class__(self.Table((((_m, _n), self.Field.sum(self[_m, _k] @ other[_k, _n] for _k in range(self.matrix_width))) for (_m, _n) in product(range(self.matrix_height), range(other.matrix_width))), [self.matrix_height, other.matrix_width], [None], [self.Field], Array=self.Array))
		else:
			return NotImplemented
	
	def __rmatmul__(self, other):
		"When math-multiplying a vector on the left by a matrix on the right, the result is an action of a transposed matrix on the vector. Element multiplications are taken in reverse order."
		
		if hasattr(other, 'field_power') and hasattr(other, 'field_base'):
			if not (self.Field.field_power == other.field_power and self.Field.field_base == other.field_base):
				raise ValueError("Multiplying matrix by a scalar from a different field.")
			return self.__class__(self.Table((((_m, _n), other @ self[_m, _n]) for (_m, _n) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		elif hasattr(other, 'vector_length'):
			if self.matrix_height != other.vector_length:
				raise ValueError("Matrix height does not equal vector length.")
			return other.__class__(other.Array((self.Field.sum(other[_m] @ self[_m, _n] for _m in range(self.matrix_height)) for _n in range(self.matrix_width)), [None], [self.Field]))
		elif hasattr(other, 'matrix_width') and hasattr(other, 'matrix_height'):
			if self.matrix_height != other.matrix_width:
				raise ValueError("Left matrix height does not equal right matrix width.")
			return self.__class__(self.Table((((_m, _n), self.Field.sum(other[_m, _k] @ self[_k, _n] for _k in range(other.matrix_width))) for (_m, _n) in product(range(other.matrix_height), range(self.matrix_width))), [other.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
		else:
			return NotImplemented
	
	def inverse(self):
		if self.matrix_width != self.matrix_height:
			raise ValueError
		
		l, u, perm = self.__ldup()
		
		while True:
			try:
				L_less_1 = self.__class__(self.Table((((i, j), self.zero_element() if i == j else l(i, j)) for (i, j) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
				D_inv = self.__class__(self.Table((((i, j), u(i, j)**-1 if i == j else self.zero_element()) for (i, j) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
				U_less_1 = self.__class__(self.Table((((i, j), self.zero_element() if i == j else u(i, j) @ u(i, i)**-1) for (i, j) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
				P_inv = self.__class__(self.Table((((i, j), self.one_element() if perm[i] == j else self.zero_element()) for (i, j) in self.keys()), [self.matrix_height, self.matrix_width], [None], [self.Field], Array=self.Array))
				break
			
			except self.__PermutationNeeded as pn:
				pn.advance()
		
		# https://mobiusfunction.wordpress.com/2010/12/08/the-inverse-of-triangular-matrix-as-a-binomial-series/
		
		L_inv = self.zero(self.matrix_height, self.matrix_width, self, self, self.Field)
		L_pow = self.one(self.matrix_height, self.matrix_width, self, self, self.Field)
		F_sgn = self.Field.one()
		while L_pow: # will converge to 0
			L_inv += F_sgn @ L_pow
			L_pow @= L_less_1
			F_sgn = -F_sgn
		
		U_inv = self.zero(self.matrix_height, self.matrix_width, self, self, self.Field)
		U_pow = self.one(self.matrix_height, self.matrix_width, self, self, self.Field)
		F_sgn = self.Field.one()
		while U_pow: # will converge to 0
			U_inv += F_sgn @ U_pow
			U_pow @= U_less_1
			F_sgn = -F_sgn
		
		return U_inv @ D_inv @ L_inv @ P_inv
	
	def __pow__(self, n):
		result = self.one(self.matrix_height, self.matrix_width, self, self, self.Field)
		if n > 0:
			for i in range(n):
				result @= self
		elif n < 0:
			inv = self.inverse()
			for i in range(abs(n)):
				result @= inv
		return result
	
	class __PermutationNeeded(BaseException):
		def __init__(self, row, perm, avoid, mat, l, u):
			self.row = row
			self.perm = perm
			self.avoid = avoid
			self.mat = mat
			self.l = l
			self.u = u
		
		def advance(self):
			self.l.clear_cache()
			self.u.clear_cache()
			
			perm = self.perm
			mat = self.mat
			r = self.row
			avoid = self.avoid
			size = len(perm)
			
			k = None
			
			for kk in range(r, size):
				#print(perm[kk], r, mat[perm[kk], r], mat[perm[r], r], [mat[perm[kk], _i] for _i in range(size)])
				if mat[perm[kk], r] != mat[perm[r], r] and perm[kk] != kk:
					k = kk
					break
			else:
				k = None
			
			#if k is None:
			#	if r != 0:
			#		print("reset", r)
			#		for i in range(size):
			#			perm[i] = i
			#		k = 0
			
			#if k is None:
			#	for kk in range(1, size):
			#		k = (r + kk) % size
			#		if perm[k] == k:
			#			break
			#	else:
			#		k = None
			
			#if k is None:
			#	for kk in range(1, size):
			#		k = (r + kk) % size
			#		if mat[perm[k], k] != avoid:
			#			break
			#	else:
			#		k = None
			
			if k is None:
				#print(perm)
				raise ArithmeticError("Could not decompose.")
			
			#print(r, k)
			
			perm[r], perm[k] = perm[k], perm[r]
	
	def __ldup(self):
		if self.matrix_width != self.matrix_height:
			raise ValueError
		
		size = self.matrix_width
		perm = [_n for _n in range(size)]
		
		def cached(f):
			c = {}
			def g(i, j):
				if (i, j) in c:
					return c[i, j]
				else:
					y = f(i, j)
					c[i, j] = y
					return y
			
			def clear_cache():
				c.clear()
			g.clear_cache = clear_cache
			
			return g
		
		perm = [_n for _n in range(size)]
		
		# https://www.geeksforgeeks.org/doolittle-algorithm-lu-decomposition/
		
		@cached
		def u(i, j):
			if i > j:
				return self.zero_element()
			
			return self[perm[i], j] - self.Field.sum(l(i, k) @ u(k, j) for k in range(i))
		
		@cached
		def l(i, j):
			if i < j:
				return self.zero_element()
			
			e = self[perm[i], j] - self.Field.sum(l(i, k) @ u(k, j) for k in range(j))
			if not e:
				return e
			
			d = u(j, j)
			if not d:
				raise self.__PermutationNeeded(j, perm, self.Field.sum(l(j, k) @ u(k, j) for k in range(j)), self, l, u)
			
			return e @ d**-1
		
		return l, u, perm
	
	def ldup_decomposition(self):
		if self.matrix_width != self.matrix_height:
			raise ValueError
		size = self.matrix_width
		
		l, u, perm = self.__ldup()
		while True:
			try:
				L = self.__class__(self.Table((((i, j), self.one_element() if i == j else l(i, j)) for (i, j) in self.keys()), [size, size], [None], [self.Field], Array=self.Array))
				D = self.__class__(self.Table((((i, j), u(i, j) if i == j else self.zero_element()) for (i, j) in self.keys()), [size, size], [None], [self.Field], Array=self.Array))
				U = self.__class__(self.Table((((i, j), self.one_element() if i == j else u(i, j) @ u(i, i)**-1) for (i, j) in self.keys()), [size, size], [None], [self.Field], Array=self.Array))
				P = self.__class__(self.Table((((i, j), self.one_element() if perm[i] == j else self.zero_element()) for (i, j) in self.keys()), [size, size], [None], [self.Field], Array=self.Array))
				return L, D, U, P
			
			except self.__PermutationNeeded as pn:
				pn.advance()
	
	def determinant(self):
		if self.matrix_width != self.matrix_height:
			raise ValueError
		size = self.matrix_width
				
		l, u, perm = self.__ldup()
		
		while True:
			try:
				d = self.Field.one()
				for i in range(size):
					d *= u(i, i)
				break
			
			except self.__PermutationNeeded as pn:
				pn.advance()
		
		for m in range(size):
			for n in range(m + 1, size):
				if perm[m] > perm[n]:
					d = -d
		
		return d


'''
class Polynomial(AbstractPolynomial):
	def __init__(self, *coefficients):
		self.Field = coefficients[0].Field
		
		if len(coefficients) > self.Field.field_size:
			short = coefficients[:self.Field.field_size]
			for n, x in enumerate(coefficients[self.Field.field_size:]):
				short[n % self.Field.field_size] += x
			super().__init__(*short)
		else:
			super().__init__(*coefficients)
'''


'''
class Polynomial:
	@property
	@cached
	def Field(self):
		return self.__values[0].Field
	
	@property
	@cached
	def Array(self):
		return array_fallback(self.__values.__class__)
	
	@classmethod
	def zero(cls, Array, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Field.zero() for _n in range(Field.field_size)), [None], [Field]))
	
	@classmethod
	def ident(cls, Array, Field):
		nArray = array_fallback(Array)
		return cls(nArray((Field.one() if _n == 1 else Field.zero() for _n in range(Field.field_size)), [None], [Field]))
	
	@classmethod
	def random(cls, Array, Field, randbelow):
		nArray = array_fallback(Array)
		return cls(nArray((randbelow(Field.field_size) for _n in range(Field.field_size)), [None], [Field]))
	
	def __init__(self, *values):
		if len(values) == 1:
			value = values[0]
			
			if isinstance(value, dict):
				assert all(((0 <= _k) and _v) for (_k, _v) in value.items())
				self.__values = value
				return
			
			try:
				self.__values = values[0].__values
				return
			except AttributeError:
				pass
			
			try:
				r, m = divmod(value, self.Field.field_size)
				v = [m]
				while r:
					r, m = divmod(r, self.Field.field_size)
					v.append(m)
				self.__values = {_n:self.Field(_v) for (_n, _v) in enumerate(v) if _v}
				return
			except (AttributeError, TypeError):
				pass
		
		self.__values = {_n:self.Field(_v) for (_n, _v) in enumerate(reversed(values)) if _v}
	
	def serialize(self):
		try:
			return self.__values.serialize()
		except AttributeError:
			return self.__values
	
	def __getitem__(self, n):
		values = self.__values
		if n in values:
			return values[n]
		else:
			return self.Field.zero()
	
	def __iter__(self):
		try:
			od = self.degree
		except ValueError:
			yield self[0]
		else:
			for n in range(od + 1):
				yield self[n]
	
	def items(self):
		for key in self.keys():
			yield key, self[key]
	
	def keys(self):
		return sorted(self.__values.keys())
	
	@property
	def degree(self):
		if self.__values:
			return max(self.__values.keys())
		else:
			raise ValueError("Zero polynomial does not have a degree.")
	
	@cached
	def __str__(self):
		if self:
			return " + ".join(reversed([f"{str(_v)}·x{superscript(_n)}" for (_n, _v) in self.items()]))
		else:
			return f"0{subscript(self.Field.field_base)}·x⁰"
	
	@cached
	def __repr__(self):
		return f'{self.__class__.__name__}({", ".join(repr(_value) for _value in self)})'
	
	def __bool__(self):
		return bool(self.__values)
	
	def __int__(self):
		r = 0
		for n, v in self.items():
			r += int(v) * self.Field.field_size ** n
		return int(r)
	
	@cached
	def __hash__(self):
		try:
			od = self.degree + 1
		except ValueError:
			od = 0
		return hash((self.__class__.__name__, tuple(self.keys()), tuple(self.items())))
	
	def __call__(self, x):
		r = self.Field.zero()
		for n, v in self.items():
			if n == 0:
				r += v
			else:
				r += v * (x ** n)
		return r
	
	def __eq__(self, other):
		try:
			return self.keys() == other.keys() and all(self[_n] == other[_n] for _n in self.keys())
		except (AttributeError, TypeError):
			return NotImplemented
	
	def __neg__(self):
		return self.__class__({_n:-_value for (_n, _value) in self.items()})
	
	def __add__(self, other):
		try:
			return self.__class__({_n:(self[_n] + other[_n]) for _n in frozenset().union(self.keys(), other.keys()) if self[_n] + other[_n]})
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			return self.__class__({_n:(self[_n] - other[_n]) for _n in frozenset().union(self.keys(), other.keys()) if self[_n] - other[_n]})
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		if not self:
			return self
		if not other:
			return other
		
		rvalues = defaultdict(lambda: self.Field.zero())
		for m, v in self.items():
			for n, w in other.items():
				rvalues[m + n] += v * w
		
		fvalues = {}
		for n, v in rvalues.items():
			if v:
				fvalues[n] = v
		
		return self.__class__(fvalues)
	
	def __divmod__(self, other):
		if not other:
			raise ZeroDivisionError("Division by zero polynomial.")
		
		if not self:
			return self, self
		
		od = other.degree
		r = other[od]
		quotient = self.__class__()
		remainder = self
		
		while remainder and (n := remainder.degree) >= od:
			d = remainder[n]
			if not d: continue
			q = self.__class__({(n - od):(d / r)})
			remainder -= q * other
			quotient += q
		
		assert (not remainder) or (other and (remainder.degree < other.degree))
		
		return quotient, remainder
	
	def __floordiv__(self, other):
		q, r = divmod(self, other)
		return q
	
	def __mod__(self, other):
		q, r = divmod(self, other)
		return r
'''




if __debug__ and __name__ == '__main__':
	from fields import Galois
	from random import randrange
	
	
	fields = Galois('Binary', 2, [1, 1]), Galois('F3', 3, [1, 0, 2, 1]), Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	#fields = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1]),

	#l = Linear([fields[2](0), fields[2](0), fields[2](2), fields[2](0), fields[2](0), fields[2](0), fields[2](0), fields[2](0)])
	#l = Linear([fields[2](252), fields[2](0), fields[2](182), fields[2](82), fields[2](64), fields[2](9), fields[2](183), fields[2](183)])
	#l = Linear.one(list, fields[2])
	#l = Linear([fields[2](0), fields[2](0), fields[2](20), fields[2](0), fields[2](0), fields[2](0), fields[2](10), fields[2](0)])
	
	#l = Linear.random(list, fields[0], randrange)
	#li = l.inverse()

	#for x in fields[0].domain():
	#	assert l(li(x)) == x
	#	assert li(l(x)) == x
	
	#print(l)
	#print(li)
	
	#quit()
	
	
	for F in fields:
		print("field", F)
		
		for w in range(1, 10):
			i = Matrix.one(w, w, dict, list, F)
			while True:
				m = Matrix.random(w, w, dict, list, F, randrange)
				
				try:
					l, d, u, p = m.ldup_decomposition()
				except ArithmeticError:
					continue
				
				for ii, jj in l.keys():
					assert l[ii, jj] == m.one_element() if ii == jj else True
					assert l[ii, jj] == m.zero_element() if ii < jj else True
				
				for ii, jj in d.keys():
					assert d[ii, jj] == m.zero_element() if ii != jj else True
				
				for ii, jj in u.keys():
					assert u[ii, jj] == m.one_element() if ii == jj else True
					assert u[ii, jj] == m.zero_element() if ii > jj else True
				
				assert l @ d @ u == p @ m
				
				try:
					n = m.inverse()
				except ArithmeticError:
					continue
				
				assert m @ n == i, f"{m} @ {n} = {m @ n}"
				assert n @ m == i, f"{n} @ {m} = {n @ m}"
				break
		
		for n in range(100):
			a = Vector.random(4, list, F, randrange)
			b = Vector.random(4, list, F, randrange)
			c = Vector.random(4, list, F, randrange)
			f = F.random(randrange)
			g = F.random(randrange)
			
			assert len(a | b) == len(a) + len(b)
			#assert a + [F(1), F(2), F(3), F(4)] == a + Vector([F(1), F(2), F(3), F(4)])
			assert a + b == b + a
			assert a - b == -(b - a)
			assert f * (a + b) == f * a + f * b
			assert f * (a - b) == f * a - f * b
			assert a @ b == b @ a
			assert a @ (b + c) == a @ b + a @ c
			assert (a + b) @ c == a @ c + b @ c
			assert (a * f) @ b == f * (a @ b)
			assert (f * a) @ b == f * (a @ b)
			assert a @ (b * f) == f * (a @ b)
			assert a @ (f * b) == f * (a @ b), f"a={a} f={f} b={b}; {a @ (f * b)} == {f * (a @ b)}"
			assert (f * a) @ (g * b) == (f * g) * (a @ b), f"a={a} f={f} b={b} g={g}; {(f * a) @ (g * b)} == {(f * g) * (a @ b)}"
		
		for n in range(10):
			a = Linear.random(list, F, randrange)
			b = Linear.random(list, F, randrange)
			c = F.random(randrange)
			cf = Linear.factor(c, list)
			d = F.random(randrange)
			df = Linear.factor(d, list)
			cdf = Linear.factor(c * d, list)
			
			for m in range(20):
				x = F.random(randrange)
				y = F.random(randrange)
				
				assert a(x + y) == a(x) + a(y)
				assert b(x + y) == b(x) + b(y)
				assert a(x - y) == a(x) - a(y)
				assert b(x - y) == b(x) - b(y)
				assert (a + b)(x) == a(x) + b(x)
				assert (a + b)(y) == a(y) + b(y)
				assert (a - b)(x) == a(x) - b(x)
				assert (a - b)(y) == a(y) - b(y)
				assert cf(x) == c * x
				assert cf(y) == c * y
				assert df(x) == d * x
				assert df(y) == d * y
				
				assert (a @ b)(x) == a(b(x))
				assert (a @ b)(y) == a(b(y))
				assert (b @ a)(x) == b(a(x))
				assert (b @ a)(y) == b(a(y))
				
				assert (a @ cf)(x) == a(cf(x))
				assert (a @ cf)(x) == a(c * x)
				assert (cf @ a)(x) == cf(a(x))
				assert (cf @ a)(x) == c * a(x)
				
				assert (a * c)(x) == c * a(x)
				assert (c * a)(x) == c * a(x)
				assert (b * c)(x) == c * b(x)
				assert (c * b)(x) == c * b(x)
				
				assert cdf(x) == c * d * x
		
		for n in range(20):
			a1 = Quadratic.random(list, Linear, F, randrange)
			a2 = Quadratic.random(list, Linear, F, randrange)
			b = Linear.random(list, F, randrange)
			c = Linear.random(list, F, randrange)
			d = Linear.random(list, F, randrange)
			e = F.random(randrange)
			
			for m in range(20):
				x = F.random(randrange)
				y = F.random(randrange)
				
				assert (d @ a1 @ (b, c))(x, y) == d(a1(b(x), c(y)))
				assert (d @ a2 @ (b, c))(x, y) == d(a2(b(x), c(y)))
				assert (a1 + a2)(x, y) == a1(x, y) + a2(x, y)
				assert (a1 - a2)(x, y) == a1(x, y) - a2(x, y)
				#print(type(a1 * e))
				assert isinstance(a1 * e, Quadratic)
				assert (a1 * e)(x, y) == e * a1(x, y)
				#print(type(e * a2))
				assert isinstance(e * a2, Quadratic)
				assert (e * a2)(x, y) == e * a2(x, y)
		
		for h in range(1, 10):
			for w in range(1, 10):
				f1 = F.random(randrange)
				f2 = F.random(randrange)
				
				vw1 = Vector.random(w, list, F, randrange)
				vw2 = Vector.random(w, list, F, randrange)
				vh1 = Vector.random(h, list, F, randrange)
				vh2 = Vector.random(h, list, F, randrange)
				
				m1 = Matrix.random(h, w, dict, list, F, randrange)
				m2 = Matrix.random(h, w, dict, list, F, randrange)
				n1 = Matrix.random(w, h, dict, list, F, randrange)
				n2 = Matrix.random(w, h, dict, list, F, randrange)
				
				assert m1 @ (f1 + f2) == m1 @ f1 + m1 @ f2
				assert (f1 + f2) @ m2 == f1 @ m2 + f2 @ m2
				assert (m1 + m2) @ f1 == m1 @ f1 + m2 @ f1
				assert f2 @ (m1 + m2) == f2 @ m1 + f2 @ m2
				
				assert m1 @ (vw1 + vw2) == m1 @ vw1 + m1 @ vw2
				assert (vh1 + vh2) @ m2 == vh1 @ m2 + vh2 @ m2
				assert (m1 + m2) @ vw1 == m1 @ vw1 + m2 @ vw1
				assert vh2 @ (m1 + m2) == vh2 @ m1 + vh2 @ m2
				
				assert m1 @ (f1 - f2) == m1 @ f1 - m1 @ f2
				assert (f1 - f2) @ m2 == f1 @ m2 - f2 @ m2
				assert (m1 - m2) @ f1 == m1 @ f1 - m2 @ f1
				assert f2 @ (m1 - m2) == f2 @ m1 - f2 @ m2
				
				assert m1 @ (vw1 - vw2) == m1 @ vw1 - m1 @ vw2
				assert (vh1 - vh2) @ m2 == vh1 @ m2 - vh2 @ m2
				assert (m1 - m2) @ vw1 == m1 @ vw1 - m2 @ vw1
				assert vh2 @ (m1 - m2) == vh2 @ m1 - vh2 @ m2
				
				assert (m1 + m2) @ n1 == m1 @ n1 + m2 @ n1
				assert m1 @ (n1 + n2) == m1 @ n1 + m1 @ n2
				assert n2 @ (m1 + m2) == n2 @ m1 + n2 @ m2
				assert (n1 + n2) @ m2 == n1 @ m2 + n2 @ m2
				
				assert (m1 - m2) @ n1 == m1 @ n1 - m2 @ n1
				assert m1 @ (n1 - n2) == m1 @ n1 - m1 @ n2
				assert n2 @ (m1 - m2) == n2 @ m1 - n2 @ m2
				assert (n1 - n2) @ m2 == n1 @ m2 - n2 @ m2
				
				assert (m1 @ n1) @ vh1 == m1 @ (n1 @ vh1)
				assert (n2 @ m2) @ vw1 == n2 @ (m2 @ vw1)
				
				if w == h and F.field_size != 2: # FIXME
					assert (m1 @ n1).determinant() == m1.determinant() * n1.determinant()


