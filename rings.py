#!/usr/bin/python3
#-*- coding:utf8 -*-

"Implementations of some rings and fields."

from collections import Counter
from itertools import chain
from algebra import AlgebraicStructure
from utils import Immutable, memoize, randbelow


__all__ = 'AbstractRing', 'ModularRing', 'BooleanRing', 'GaloisField', 'BinaryField', 'RijndaelField'


class AbstractRing(Immutable, AlgebraicStructure):
	"Base class of rings."
	
	algebra_kwparams_names = ('size',)
	
	def __init__(self, *args, **kwargs):
		AlgebraicStructure.__init__(self, *args, **kwargs)
		self.immutable = True
	
	@classmethod
	def zero(cls, *args, **kwargs):
		return cls(0, *args, **kwargs)
	
	@classmethod
	def one(cls, *args, **kwargs):
		return cls(1, *args, **kwargs)
	
	@classmethod
	def sum(cls, addends, *args, **kwargs):
		result = cls.zero(*args, **kwargs)
		for addend in addends:
			result += addend
		return result
	
	@classmethod
	def product(cls, factors, *args, **kwargs):
		result = cls.one(*args, **kwargs)
		for factor in factors:
			result *= factor
		return result
	
	@classmethod
	def random(cls, *args, **kwargs):
		"Return random ring element."
		size = cls.get_algebra(*args, **kwargs).size
		return cls(randbelow(size), *args, **kwargs)
	
	@classmethod
	def random_nonzero(cls, *args, **kwargs):
		"Return nonzero random ring element."
		size = cls.get_algebra(*args, **kwargs).size
		return cls(randbelow(size - 1) + 1, *args, **kwargs)
	
	@classmethod
	def domain(cls, *args, **kwargs):
		"Yield all possible values of this ring."
		size = cls.get_algebra(*args, **kwargs).size
		for i in range(size):
			yield cls(i, *args, **kwargs)
	
	def __hash__(self):
		if __debug__: super().__hash__() # call superclass to ensure the object has been initialized properly, especially when unpickling
		return hash(int(self))
	
	def __bool__(self):
		return bool(int(self))
	
	def __int__(self):
		raise NotImplementedError("Could not convert ring value to int.")
	
	def is_zero(self):
		return int(self) == 0
	
	def is_one(self):
		return int(self) == 1
	
	def sort_ordering(self):
		"String returned here affects the ordering of terms in `canonical`."
		return f"9{int(self):08d}"
	
	def __eq__(self, other):
		if self is other: return True
		
		try:
			if self.algebra != other.algebra:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		self_canonical = self.canonical()
		other_canonical = other.canonical()
		
		return self_canonical.ring_value == other_canonical.ring_value
	
	def __gt__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		self_canonical = self.canonical()
		other_canonical = other.canonical()
		
		return int(self_canonical) > int(other_canonical)
	
	def __add__(self, other):
		raise NotImplementedError
	
	def __sub__(self, other):
		raise NotImplementedError
	
	def __neg__(self):
		raise NotImplementedError
	
	def __mul__(self, other):
		raise NotImplementedError
	
	def __divmod__(self, other):
		"Return a pair `a`, `b` such that `a * other + b = self`."
		
		if self.algebra != other.algebra:
			return NotImplemented
		
		if other.is_zero():
			raise ZeroDivisionError("Zero element used in a modulus or division.")
		
		if self.is_zero():
			return self.algebra.zero(), self.algebra.zero()
		
		quotient = self.algebra.zero()
		modulus = self.algebra(self.algebra.size - 1)
		for r in self.algebra.domain(): # exhaustive search
			nm = r * other - self
			if nm < modulus:
				quotient = r
				modulus = nm
			if modulus.is_zero(): break
		
		return quotient, modulus
	
	def __truediv__(self, other):
		quotient, remainder = divmod(self, other)
		if remainder:
			raise ArithmeticError(f"`{other}` is not a divisor of `{self}` (`{self} = {quotient} * {other} + {remainder}`).")
		return quotient
	
	def __floordiv__(self, other):
		quotient, remainder = divmod(self, other)
		return quotient
	
	def __mod__(self, other):
		quotient, remainder = divmod(self, other)
		return remainder
	
	def __or__(self, other):
		"Return 'disjunction' of Galois field elements, defined as `x + y - x * y`."
		return self + other - self * other
	
	def __pow__(self, exponent, modulus=None):
		"Raise `self` to the power of `exponent:int` modulo optional `modulus:int`."
		
		if modulus != None:
			if modulus > self.algebra.size:
				raise ArithmeticError("Modulus ({}) greater than the field size ({}) in pow() operator.".format(modulus, self.size))
			
			if not modulus:
				raise ZeroDivisionError("Zero modulus in pow() operator.")
			
			if modulus == 1:
				return self.algebra.zero()
			
			if modulus <= 0:
				raise ArithmeticError("Modulus must be >= 2 (got {}).".format(modulus))
		
		if (not self) and (not exponent):
			raise ZeroDivisionError("Zero to the power of zero.")
		
		if not self:
			return self.algebra.zero()
		
		if exponent >= 0:
			base = self
		else:
			base = self.algebra.one() / self
		
		result = self.algebra.one()
		
		for i in range(abs(exponent)):
			result *= base
		
		if modulus == None:
			return result
		else:
			return result % self.algebra(modulus)
	
	def evaluate(self):
		return self
	
	def canonical(self):
		raise NotImplementedError
	
	def is_jit(self):
		raise NotImplementedError
	
	def optimized(self):
		return self


class ModularRing(AbstractRing):
	"Ring of integers modulo certain number. Values represented as `int` objects."
	
	def __init__(self, value, *args, size=None, **kwargs):
		if size == None:
			size = value.algebra.size
		
		if size < 2:
			raise ValueError("`size` must be greater or equal to 2. (got {})".format(size))
		
		try:
			ring_value = value.ring_value
		except AttributeError:
			if hasattr(value, 'jit_value') and value.jit_value.type.width == 1 and size == 2:
				ring_value = value
			else:
				ring_value = value % size
		
		if not hasattr(self, 'ring_value'):
			self.ring_value = ring_value
		
		super().__init__(ring_value, *args, size=size, **kwargs)
	
	def __getnewargs_ex__(self):
		return (self.ring_value,), {'size':self.algebra.size}
	
	def is_jit(self):
		return hasattr(self.ring_value, 'jit_value')
	
	def __int__(self):
		return int(self.ring_value)
	
	def __add__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
			return self.algebra(self.ring_value + other.ring_value)
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
			return self.algebra(self.algebra.size + self.ring_value - other.ring_value)
		except AttributeError:
			return NotImplemented
	
	def __neg__(self):
		return self.algebra(self.algebra.size - self.ring_value)
	
	def __mul__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
			return self.algebra(self.ring_value * other.ring_value)
		except AttributeError:
			return NotImplemented
	
	def __divmod__(self, other):
		"Return a pair `a`, `b` such that `a * other + b = self`."
		
		try:
			if self.algebra != other.algebra:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		if not other:
			raise ZeroDivisionError("Zero element used in a modulus or division.")
		
		if not self:
			return self.algebra.zero(), self.algebra.zero()
		
		quotient = 0
		modulus = self.algebra.size - 1
		other_ring_value = other.ring_value
		self_ring_value = self.ring_value
		size = self.algebra.size
		for r in range(size): # TODO: exhaustive search, needs improvement
			nm = (size + r * other_ring_value - self_ring_value) % size
			if nm < modulus:
				quotient = r
				modulus = nm
			if not nm: break
		
		return self.algebra(quotient), self.algebra(modulus)
	
	def canonical(self):
		return self
	
	def __repr__(self):
		return ''.join(['<', self.__class__.__qualname__, ': ', str(self.ring_value), ', ', repr(self.algebra), '>'])
		#return self.__class__.__qualname__ + '(' + str(self.operator) + ', ' + repr(self.operands) + ')'
	
	def __str__(self):
		return str(int(self))


class BooleanRing(ModularRing):
	"Boolean ring: Only 2 values (`yes` and `no`), addition is XOR, multiplication is AND. Values represented as `bool` objects."
	
	def __getnewargs__(self):
		return bool(self),
	
	def __new__(cls, value, *args, **kwargs):
		try:
			if hasattr(value, 'jit_value'):
				pass
			elif value is cls.yes:
				return cls.yes
			elif value is cls.no:
				return cls.no
			elif value % 2:
				return cls.yes
			elif not (value % 2):
				return cls.no
			else:
				raise RuntimeError
		except AttributeError:
			pass
		
		return object.__new__(cls)
	
	def __init__(self, value, *args, **kwargs):
		if self.immutable: return # don't redo initialization when `BooleanRing.yes` or `BooleanRing.no` has been returned from `__new__`
		
		if 'size' in kwargs:
			assert kwargs['size'] == 2
			del kwargs['size']
		
		if not hasattr(value, 'jit_value'):
			try:
				value = bool(value % 2)
			except TypeError:
				value = value % 2
		
		super().__init__(value, *args, size=2, **kwargs)
	
	@classmethod
	def zero(cls, *args, **kwargs):
		return cls.no
	
	@classmethod
	def one(cls, *args, **kwargs):
		return cls.yes
	
	@classmethod
	def get_algebra(cls, *params, **kwparams):
		try:
			if kwparams['size'] not in (2, None):
				raise ValueError("`size`, if provided, must be 2 or None.")
		except KeyError:
			pass
		kwparams['size'] = 2
		return super(BooleanRing, cls).get_algebra(*params, **kwparams)
	
	def __add__(self, other):
		yes = self.yes
		no = self.no
		if ((self is yes) or (self is no)) and ((other is yes) or (other is no)):
			return yes if self.ring_value ^ other.ring_value else no
		
		try:
			if self.algebra != other.algebra:
				return NotImplemented
			return self.algebra(self.ring_value ^ other.ring_value)
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		return self.__add__(other)
	
	def __neg__(self):
		return self
	
	def __or__(self, other):
		yes = self.yes
		no = self.no
		if ((self is yes) or (self is no)) and ((other is yes) or (other is no)):
			return yes if self.ring_value | other.ring_value else no

		try:
			if self.algebra != other.algebra:
				return NotImplemented
			return self.algebra(self.ring_value | other.ring_value)
		except AttributeError:
			return NotImplemented
	
	def __mul__(self, other):
		yes = self.yes
		no = self.no
		if ((self is yes) or (self is no)) and ((other is yes) or (other is no)):
			return yes if self.ring_value & other.ring_value else no
		
		try:
			if self.algebra != other.algebra:
				return NotImplemented	
			return self.algebra(self.ring_value & other.ring_value)
		except AttributeError:
			return NotImplemented

BooleanRing.no = BooleanRing(False)
BooleanRing.yes = BooleanRing(True)


class GaloisField(AbstractRing):
	"Galois (finite) fields. Fields are rings and also every nonzero element has an inverse. Values represented as lists of integers."
	
	algebra_kwparams_names = AbstractRing.algebra_kwparams_names + ('base', 'exponent', 'reducing_polynomial')
	
	@classmethod
	def __decode_args(cls, value, *args, size=None, base=None, exponent=None, reducing_polynomial=None, **kwargs):
		if all(_x == None for _x in (size, base, exponent, reducing_polynomial)):
			try:
				size = value.algebra.size
				base = value.algebra.base
				exponent = value.algebra.exponent
				reducing_polynomial = value.algebra.reducing_polynomial
			except AttributeError:
				pass
		
		if reducing_polynomial != None:
			try:
				good = reducing_polynomial[-1] == 1 or reducing_polynomial[-1].is_one()
			except AttributeError:
				good = False
			
			if not good:
				raise ValueError("Leading term of the reducing polynomial must not be 0.")
		
		if exponent == None and reducing_polynomial != None:
			exponent = len(reducing_polynomial) - 1
		
		if base == None and reducing_polynomial != None:
			try:
				base = reducing_polynomial[0].algebra.size
			except AttributeError:
				pass
		
		if (base == None or exponent == None) and size != None:
			factorization = Counter()
			s = size
			while s > 1:
				for n in range(2, s + 1):
					if s % n == 0:
						s //= n
						factorization[n] += 1
						break
			del s
			if len(list(factorization.keys())) != 1:
				raise ValueError("`size` must be a power of a prime. factorization: {} = {}".format(size, " * ".join((str(_b) + "**" + str(_e)) for (_b, _e) in factorization.items())))
			
			b, e = list(factorization.items())[0]
			
			if base == None:
				base = b
			else:
				if base != b:
					raise ValueError("`base = {}` value does not match with `size = {}` value. `base` must be prime and `size` must be a natural power of `base`.".format(base, size))
			
			if exponent == None:
				exponent = e
			else:
				if exponent != e:
					raise ValueError("`exponent = {}` value does not match with `size = {}` value. `size` must be prime raised to the power of `exponent`.".format(exponent, size))
		
		if size == None:
			if base != None and exponent != None:
				size = base**exponent
			else:
				raise TypeError("Provided arguments are not enough to determine field parameters. (Provide the size at least.)")
		
		if size < 2:
			raise ValueError("`size` must be greater or equal to 2. (got {})".format(size))
		
		if reducing_polynomial == None:
			reducing_polynomial = [0] * (exponent + 1)
			reducing_polynomial[-1] = 1
			if size == 2:
				reducing_polynomial[0] = 1
			else:
				raise NotImplementedError("Implement calculation of reducing polynomial.") # TODO
		
		if len(reducing_polynomial) != exponent + 1:
			raise ValueError("Reducing polynomial ({}) must have the degree `exponent = {}`.".format(reducing_polynomial, exponent))
		
		field_value = None
		
		if value != None:
			if field_value == None:
				if value == Ellipsis:
					field_value = value
			
			if field_value == None:
				try:
					field_value = value.field_value
				except AttributeError:
					pass
			
			if field_value == None:
				try:
					components = []
					for v in value:
						components.append(v % base)
					field_value = tuple(components)
				except TypeError:
					pass
			
			if field_value == None:
				try:
					vs = int(value)
					if vs < 0:
						raise ValueError("Integer `value = {}` to decode in Galois field must be greater or equal to 0.".format(vs))
					
					if vs >= size:
						vs %= size
					
					components = []
					for i in range(exponent):
						component = vs % base
						vs //= base
						components.append(component)
					
					assert len(components) <= exponent
					
					components.extend([0] * (exponent - len(components)))
					
					field_value = tuple(components)
				except TypeError:
					pass
		
		return field_value, int(size), int(base), int(exponent), tuple(reducing_polynomial)
	
	def __init__(self, *args, **kwargs):
		field_value, size, base, exponent, reducing_polynomial = self.__decode_args(*args, **kwargs)
		
		if field_value == None:
			raise TypeError("`value` must be a collection of ints, an integer, or another field object.")
		
		if field_value != Ellipsis and len(field_value) != exponent:
			raise ValueError("Field value vector ({}) must have the same lengt as `exponent = {}`.".format(len(field_value), exponent))
		
		if not hasattr(self, 'field_value'):
			self.field_value = field_value
		
		super().__init__(*args, **kwargs)
	
	@classmethod
	def get_algebra(cls, *args, **kwargs):
		field_value, size, base, exponent, reducing_polynomial = cls.__decode_args(*((None,) + args), **kwargs)
		
		for kwarg in 'field_value', 'size', 'base', 'exponent', 'reducing_polynomial':
			try:
				del kwargs[kwarg]
			except KeyError:
				pass
		
		return super(GaloisField, cls).get_algebra(*args, size=size, base=base, exponent=exponent, reducing_polynomial=reducing_polynomial, **kwargs)
	
	def __getnewargs_ex__(self):
		return (self.field_value), {'base':self.algebra.base, 'reducing_polynomial':self.algebra.reducing_polynomial}
	
	def __str__(self):
		return ":".join(reversed([str(_v) for _v in self.field_value]))
	
	def __int__(self):
		return self.ring_value
	
	def __bool__(self):
		return not self.is_zero()
	
	@property
	def ring_value(self):
		if self.is_jit():
			raise AttributeError
		value = 0
		for v in reversed(self.field_value):
			value *= self.algebra.base
			value += v
		return value
	
	@ring_value.setter
	def ring_value(self, value):
		if self.is_jit():
			assert value == Ellipsis
			return
		assert self.ring_value == value
	
	def is_jit(self):
		return hasattr(self.field_value, 'jit_value')
	
	def is_zero(self):
		return all(_v == 0 for _v in self.field_value)
	
	def is_one(self):
		return self.field_value[0] == 1 and all(_v == 0 for _v in self.field_value[1:])
	
	def __add__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		components_a = self.field_value
		components_b = other.field_value
		l = max(len(components_a), len(components_b))
		base = self.algebra.base
		result = []
		for a, b in zip(chain(components_a, [0] * (l - len(components_a))), chain(components_b, [0] * (l - len(components_b)))):
			s = (a + b) % base
			result.append(s)
		
		return self.algebra(result)
	
	def __sub__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
		except AttributeError:
			return NotImplemented	
			
		components_a = self.field_value
		components_b = other.field_value
		l = max(len(components_a), len(components_b))
		base = self.algebra.base
		result = []
		for a, b in zip(chain(components_a, [0] * (l - len(components_a))), chain(components_b, [0] * (l - len(components_b)))):
			s = (base + a - b) % base
			result.append(s)
		
		return self.algebra(result)
	
	def __neg__(self):
		base = self.algebra.base
		result = []
		for c in self.field_value:
			s = (base + c) % base
			result.append(s)
		
		return self.algebra(result)
	
	@staticmethod
	def long_multiplication(this, other):
		"Long multiplication algorithm (slow)."
		
		try:
			if this.algebra != other.algebra:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		algebra = this.algebra
		base = algebra.base
		exponent = algebra.exponent
		reducing_polynomial = algebra.reducing_polynomial
		
		a = list(this.field_value)
		b = list(other.field_value)
		
		result = [0] * (2 * exponent)
		
		for m, aa in enumerate(a):
			for n, bb in enumerate(b):
				result[m + n] += (aa * bb)
				result[m + n] %= base
		
		for m in reversed(range(exponent)):
			if result[m + exponent]:
				for n in reversed(range(exponent)):
					result[m + n] = (base + result[m + n] - reducing_polynomial[n]) % base
		
		assert all((_v == 0) for _v in result[exponent:])
		assert all((0 <= _v < base) for _v in result[:exponent])
		
		return algebra(result[:exponent])
	
	def __divmod__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		if not other:
			raise ZeroDivisionError("Division / modulo by zero element of Galois field.")
		
		if not self:
			return self.algebra.zero(), self.algebra.zero()
		
		for oi in self.algebra.domain():
			assert oi.is_zero() or (not (oi * other).is_zero()), "Zero divisor in Galois field. (Bad reducing polynomial?)"
			if (oi * other).is_one():
				other_inverse = oi
				break
		else:
			assert False, "Could not find inverse in Galois field."
		
		return self * other_inverse, self.algebra.zero()
	
	def canonical(self):
		return self
	
	@memoize
	def is_multiplicative_generator(self):
		if self.is_zero():
			return False
		elif self.is_one():
			return self.algebra.size == 2
		else:
			elements = set()
			power = self.algebra.one()
			for n in range(self.algebra.size - 1):
				elements.add(power)
				assert self.algebra.zero() not in elements
				power = self.long_multiplication(self, power)
			return len(elements) == self.algebra.size - 1
	
	@classmethod
	@memoize # TODO: test memoization
	def smallest_multiplicative_generator(cls, *args, **kwargs):
		for g in cls.domain(*args, **kwargs):
			if g.is_multiplicative_generator():
				return g
		raise ArithmeticError("No multiplicative generator found.")
	
	def __pow__(self, exponent, modulus=None):
		if self == self.algebra.smallest_multiplicative_generator() and modulus == None:
			return self.algebra.exp(exponent)
		else:
			result = self.algebra.one()
			if exponent >= 0:
				base = self
			else:
				base = self.algebra.one() / self
			for n in range(abs(exponent)):
				result = self.long_multiplication(result, base)
				if modulus != None:
					result = result % modulus
			return result
	
	@classmethod
	@memoize # TODO: test memoization
	def exp(cls, ee, *args, **kwargs):
		"Exponent relative to the smallest multiplicative generator."
		
		result = cls.one(*args, **kwargs)
		
		if ee >= 0:
			base = cls.smallest_multiplicative_generator(*args, **kwargs)
		else:
			base = cls.one(*args, **kwargs) / cls.smallest_multiplicative_generator(*args, **kwargs)
		
		for n in range(ee):
			result = cls.long_multiplication(result, base)
		
		return result
	
	@memoize
	def log(self):
		"Logarithm relative to the smallest multiplicative generator."
		
		if self.is_zero(): raise ZeroDivisionError("Logarithm of 0 element of Galois field does not exist.")
		
		power = self.algebra.one()
		for m in range(self.algebra.size):
			if power == self:
				return m
			power = self.long_multiplication(self.algebra.smallest_multiplicative_generator(), power)
		else:
			raise ArithmeticError("Logarithm not found for element `{}`. Field size: {}.".format(str(self), self.algebra.size))
	
	@staticmethod
	def slipstick_multiplication(one, two):
		"Fast multiplication algorithm exploiting the identity `a * b = exp(log(a) + log(b))`. Needs working 'long multiplication' algorithm for logarithm and exponent table."
		
		if one.algebra != two.algebra:
			raise ValueError
		
		if one.is_jit() or two.is_jit():
			exp_table = one.algebra.jit_exp_table
			log_table = one.algebra.jit_log_table
			
			if one.is_jit():
				try:
					first = one.field_value
				except AttributeError:
					first = one.binary_field_value
			else:
				first = int(one)
			
			if two.is_jit():
				try:
					second = two.field_value
				except AttributeError:
					second = two.binary_field_value
			else:
				second = int(two)
			
			return one.algebra((first * second != 0) * exp_table[(log_table[first] + log_table[second]) % (one.algebra.size - 1)])
		
		if one.is_zero() or two.is_zero():
			return one.algebra.zero()
		
		return one.algebra.exp((one.log() + two.log()) % (one.algebra.size - 1))
	
	def __mul__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
		except AttributeError:
			return NotImplemented
		
		#if __debug__:
		#	l = self.long_multiplication(self, other)
		#	s = self.slipstick_multiplication(self, other)
		#	assert l == s
		#	return s
		
		try:
			return self.slipstick_multiplication(self, other)
		except AttributeError:
			return self.long_multiplication(self, other)
	
	@classmethod
	def log_exp_tables(cls, *args, **kwargs):
		algebra = cls.get_algebra(*args, **kwargs)
		log_table = [0] * algebra.size
		exp_table = [0] * algebra.size
		for m in algebra.domain():
			try:
				l = m.log()
			except ZeroDivisionError:
				continue
			assert 0 <= l <= 255
			
			b = int(m)
			assert 1 <= b <= 256
			
			log_table[b] = l
			exp_table[l] = b
		return log_table, exp_table
	
	@classmethod
	def compile_tables(cls, name, compiler, *args, **kwargs):
		"""
		Compile exponent and logarithm tables. If this method is called, compiled circuits will use slipstick multiplication.
		If not, they will default to long multiplication. It varies between system which algorithm is faster.
		"""
		algebra = cls.get_algebra(*args, **kwargs)
		log_table, exp_table = algebra.log_exp_tables()
		bits = (algebra.size - 1).bit_length()
		
		from jit_types import HardwareType
		Type = HardwareType(bits)
		
		compiler[name + '.jit_log_table'] = Type[len(log_table)](*log_table)
		algebra.jit_log_table = compiler[name + '.jit_log_table']
		compiler[name + '.jit_exp_table'] = Type[len(exp_table)](*exp_table)
		algebra.jit_exp_table = compiler[name + '.jit_exp_table']


class BinaryField(GaloisField):
	"Galois field over Boolean ring with efficient representation as bitfields."
	
	algebra_kwparams_names = GaloisField.algebra_kwparams_names + ('reducing_polynomial_bitfield',)
	
	@classmethod
	def __decode_args(cls, value, *args, size=None, exponent=None, reducing_polynomial=None, reducing_polynomial_bitfield=None, **kwargs):
		try:
			reducing_polynomial_bitfield = value.algebra.reducing_polynomial_bitfield
		except AttributeError:
			pass
		
		if reducing_polynomial_bitfield == None:
			algebra = GaloisField.get_algebra(*args, size=size, base=2, exponent=exponent, reducing_polynomial=reducing_polynomial, **kwargs)
			
			size = algebra.size
			assert algebra.base == 2
			exponent = algebra.exponent
			reducing_polynomial = algebra.reducing_polynomial
			
			del algebra
		
		assert (reducing_polynomial != None) or (reducing_polynomial_bitfield != None)
		
		if reducing_polynomial != None:
			rpb = 0
			for n, v in enumerate(reducing_polynomial):
				if not ((v == 0) or (v == 1) or (v.is_zero()) or (v.is_one())):
					raise ValueError("Reducing polynomial must consist only of 0 and 1.")
				rpb <<= 1
				rpb |= v
		else:
			rpb = reducing_polynomial_bitfield
			reducing_polynomial = tuple((rpb >> _n) & 1 for _n in range(rpb.bit_length()))
		
		if reducing_polynomial_bitfield == None:
			reducing_polynomial_bitfield = rpb
		else:
			if reducing_polynomial_bitfield != rpb:
				raise ValueError("`reducing_polynomial` and `reducing_polynomial_bitfield` do not match.")
		
		binary_field_value = None
		
		if binary_field_value == None:
			try:
				binary_field_value = value.binary_field_value
			except AttributeError:
				pass
		
		if binary_field_value == None:
			try:
				try:
					vs = value.field_value
				except AttributeError:
					vs = value
				
				bfv = 0
				for v in vs:
					bfv <<= 1
					if not ((v == 0) or (v == 1) or (v.is_zero()) or (v.is_one())):
						raise ValueError("Elements of `value` argument must be equal to 0 or 1.")
					bfv |= int(v)
				binary_field_value = bfv
			except TypeError:
				pass
		
		if binary_field_value == None:
			try:
				binary_field_value = int(value)
			except TypeError:
				pass
		
		if binary_field_value == None:
			if hasattr(value, 'jit_value'):
				binary_field_value = value
		
		return binary_field_value, size, exponent, reducing_polynomial, reducing_polynomial_bitfield
	
	def __init__(self, value, *args, size=None, exponent=None, reducing_polynomial=None, reducing_polynomial_bitfield=None, **kwargs):
		binary_field_value, size, exponent, reducing_polynomial, reducing_polynomial_bitfield = self.__decode_args(value, *args, size=size, exponent=exponent, reducing_polynomial=reducing_polynomial, reducing_polynomial_bitfield=reducing_polynomial_bitfield, **kwargs)
		
		if binary_field_value == None:
			raise TypeError("`value` argument must either be an int (bitfield), collection of 0 and 1, or another field.")
		
		self.binary_field_value = binary_field_value % size
		
		for kwarg in 'binary_field_value', 'size', 'base', 'exponent', 'reducing_polynomial', 'reducing_polynomial_bitfield':
			try:
				del kwargs[kwarg]
			except KeyError:
				pass
		
		if self.is_jit():
			value = Ellipsis
		super().__init__(value, *args, size=size, base=2, exponent=exponent, reducing_polynomial=reducing_polynomial, reducing_polynomial_bitfield=reducing_polynomial_bitfield, **kwargs)
	
	@classmethod
	def get_algebra(cls, *args, **kwargs):
		binary_field_value, size, exponent, reducing_polynomial, reducing_polynomial_bitfield = cls.__decode_args(*((None,) + args), **kwargs)
		
		for kwarg in 'binary_field_value', 'size', 'base', 'exponent', 'reducing_polynomial', 'reducing_polynomial_bitfield':
			try:
				del kwargs[kwarg]
			except KeyError:
				pass
		
		return super(BinaryField, cls).get_algebra(*args, size=size, base=2, exponent=exponent, reducing_polynomial=reducing_polynomial, reducing_polynomial_bitfield=reducing_polynomial_bitfield, **kwargs)
	
	def __getnewargs_ex__(self):
		return (self.binary_field_value,), {'reducing_polynomial_bitfield':self.algebra.reducing_polynomial_bitfield}
	
	@property
	def field_value(self):
		if self.is_jit():
			raise AttributeError
			return
		value = []
		for n in range(self.algebra.exponent):
			value.append(1 if (self.binary_field_value & (1 << n)) else 0)
		return value
	
	@field_value.setter
	def field_value(self, value):
		if self.is_jit():
			assert value == Ellipsis
			return
		try:
			assert self.field_value == value
		except AttributeError:
			pass
	
	def __str__(self):
		val = bin(self.binary_field_value)[2:]
		lz = '0' * (self.algebra.exponent - len(val))
		return '0b' + lz + val
	
	def __int__(self):
		return int(self.binary_field_value)
	
	def is_jit(self):
		return hasattr(self.binary_field_value, 'jit_value')
	
	def is_zero(self):
		return self.binary_field_value == 0
	
	def is_one(self):
		return self.binary_field_value == 1
	
	def __add__(self, other):
		try:
			if self.algebra != other.algebra:
				return NotImplemented
			return self.algebra(self.binary_field_value ^ other.binary_field_value)
		except AttributeError:
			return NotImplemented
	
	def __sub__(self, other):
		return self.__add__(other)
	
	def __neg__(self):
		return self
	
	@staticmethod
	def long_multiplication(one, two):
		"Long multiplication algorithm for binary fields, where ADD = XOR."
		
		if one.algebra != two.algebra:
			raise ValueError
		
		algebra = one.algebra
		
		if one.is_zero() or two.is_zero():
			return algebra.zero()
		
		a = one.binary_field_value
		b = two.binary_field_value
		
		exponent = algebra.exponent
		
		value = 0
		for m in range(exponent):
			for n in range(exponent):
				value ^= ((a >> m) & (b >> n) & 1) << (m + n)
		
		reducing_polynomial_bitfield = algebra.reducing_polynomial_bitfield
		
		for m in reversed(range(exponent)):
			value ^= (reducing_polynomial_bitfield << m) * ((value >> (m + exponent)) & 1)
		
		assert one.is_jit() or two.is_jit() or 0 <= value < algebra.size
		
		return algebra(value)


# Rijndael field, used in AES encryption standard.
RijndaelField = BinaryField.get_algebra(exponent=8, reducing_polynomial=(1, 0, 0, 0, 1, 1, 0, 1, 1))

assert BinaryField.get_algebra(exponent=1)(1) != RijndaelField(1)


if __debug__:
	import pickle
	from itertools import product
	
	def test_ring(Ring):
		"Test suite for rings."
		
		yes = Ring.one()
		no = Ring.zero()
		
		assert yes.algebra == no.algebra == Ring
		
		try:
			algebra_size = Ring.size
		except AttributeError:
			algebra_size = Ring.base_ring.size
		
		#if algebra.size == 2:
		#	assert yes is Ring.yes
		#	assert no is Ring.no
		#	
		#	assert pickle.loads(pickle.dumps(yes)) is yes
		#	assert pickle.loads(pickle.dumps(no)) is no
		#else:
		assert pickle.loads(pickle.dumps(yes)) == yes
		assert pickle.loads(pickle.dumps(no)) == no
		
		assert hash(pickle.loads(pickle.dumps(yes))) == hash(yes)
		assert hash(pickle.loads(pickle.dumps(no))) == hash(no)
		
		assert yes != no
		assert yes.ring_value != no.ring_value
		
		assert no.is_zero()
		assert yes.is_one()
		assert not no
		assert yes
		
		assert yes * yes == yes
		assert yes * no == no
		assert no * yes == no
		assert no * no == no
		
		if algebra_size == 2:
			assert yes + yes == no
		
		assert yes + no == yes
		assert no + yes == yes
		assert no + no == no
		
		assert sum([yes for _i in range(algebra_size)], no) == no, str(sum([yes for _i in range(algebra_size)], no).canonical())
		assert sum([yes for _i in range(algebra_size + 1)], no) == yes
		
		assert yes // yes == yes
		assert no // yes == no
		
		try:
			something = yes // no
			assert False, "Expected ZeroDivisionError when dividing by zero, got `{}`.".format(str(something))
		except ZeroDivisionError:
			pass
		
		try:
			something = no // no
			assert False, "Expected ZeroDivisionError when dividing by zero, got `{}`.".format(str(something))
		except ZeroDivisionError:
			pass
		
		assert yes % yes == no
		assert no % yes == no
		
		try:
			yes % no
			assert False
		except ZeroDivisionError:
			pass
		
		try:
			no % no
			assert False
		except ZeroDivisionError:
			pass
		
		assert divmod(yes, yes) == (yes // yes, yes % yes)
		assert divmod(no, yes) == (no // yes, no % yes)
		
		assert max([yes, yes]) == yes
		assert max([yes, no]) == yes
		assert max([no, no]) == no
		assert min([yes, yes]) == yes
		assert min([yes, no]) == no
		assert min([no, no]) == no
		
		for n in range(10):
			r = Ring.random()
			assert 0 <= int(r) < algebra_size
		
		for n in range(10):
			r = Ring(n)
			#print(int(r), n, algebra_size, Ring)
			assert int(r) == n % algebra_size
		
		'''
		for x in Ring.domain():
			assert x == x
			assert x + no == x
			assert x + yes != x
			assert x - x == no
			assert x + (-x) == no
		
		for x, y in product(Ring.domain(), Ring.domain()):
			assert x + y == y + x
			assert x - y == x + (-y)
			assert x | y == x + y - x * y
		
		for x, y, z in product(Ring.domain(), Ring.domain(), Ring.domain()):
			assert (x + y) + z == x + (y + z)
			assert x * (y + z) == x * y + x * z
			assert (x + y) * z == x * z + y * z
		'''
	
	def test_field(Field):
		for x in Field.domain():
			try:
				x**-1 * x == Field.one()
			except ZeroDivisionError:
				assert not x
			except ArithmeticError:
				assert False, "Field value does not have an inverse: x = {}".format(str(x))
		
		#@check
		#def disjunction(x:Field, y:Field):
		#	assert x | y == x + y - x * y
		
		# TODO: move this to GaloisField
		#assert Field.smallest_multiplicative_generator() > Field.zero()
		#for g in Field.domain():
		#	if g.is_zero(): continue
		#	assert Field.exp(g.log()) == g
	
	
	def rings_test_suite(verbose=False):
		if verbose: print("running test suite")
		
		for i in chain(range(2, 64), (2**_i for _i in range(7, 16))):
			if verbose: print()
			if verbose: print("test ModularRing(size={})".format(i))
			ring = ModularRing.get_algebra(size=i)
			if verbose: print(" ring test")
			test_ring(ring)
		
		if verbose: print()
		if verbose: print("test BooleanRing()")
		ring = BooleanRing.get_algebra()
		assert not ring(0)
		assert ring(1)
		assert not ring(2)
		assert ring(3)
		assert not ring(False)
		assert ring(True)
		if verbose: print(" ring test")
		test_ring(ring)
		
		for i in (2,): #(3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 18, 19, 23, 25, 32, 49, 64, 81, 121, 128, 256, 52, 1024):
			if verbose: print()
			if verbose: print("test GaloisField(size={})".format(i))
			field = GaloisField.get_algebra(size=i)
			if verbose: print(" ring test")
			test_ring(field)
			if verbose: print(" field test")
			test_field(field)
		
		for i in (1,): #(2, 3, 4, 5, 6, 7, 8, 16, 32, 64):
			if verbose: print()
			if verbose: print("test BinaryField(exponent={})".format(i))
			field = BinaryField.get_algebra(exponent=i)
			if verbose: print(" ring test")
			test_ring(field)
			if verbose: print(" field test")
			test_field(field)
		
		if verbose: print()
		if verbose: print("test RijndaelField()")
		field = RijndaelField
		
		if verbose: print(" ring test")
		test_ring(field)
		if verbose: print(" field test")
		test_field(field)
	
	__all__ = __all__ + ('test_ring', 'test_field', 'rings_test_suite')


if __debug__ and __name__ == '__main__':
	rings_test_suite(verbose=True)



