#!/usr/bin/python3
#-*- coding:utf8 -*-


from itertools import chain
from utils import Immutable


__all__ = 'Algebra', 'AlgebraicStructure'


class Algebra(Immutable):
	"An object representing the algebra, that means the set of values and operations on that values. Makes sense only coupled with the class implementing the neccessary operations."
	
	mutable = frozenset(['hash_cache', 'jit_log_table', 'jit_exp_table'])
	
	def __init__(self, name, init, params, kwparams):
		self.algebra_name = name
		if isinstance(init, str):
			self.algebra_init = globals()[init] # recover init function from its name (unpickle protocol)
		else:
			self.algebra_init = init
		
		self.algebra_params = params[len(params)-init.algebra_params_count:]
		self.algebra_kwparams = dict((_k, _v) for (_k, _v) in kwparams.items() if (_k in init.algebra_kwparams_names))
		
		if len(self.algebra_params) != init.algebra_params_count:
			raise TypeError("Provide all positional arguments for algebra instance. Required: {}, got: {}.".format(init.algebra_params_count, len(self.algebra_params)))
		
		if frozenset(self.algebra_kwparams.keys()) != frozenset(init.algebra_kwparams_names):
			raise TypeError("Provide all keyword arguments for algebra instance. Missing arguments: {}.".format(", ".join(frozenset(init.algebra_kwparams_names) - frozenset(self.algebra_kwparams.keys()))))
		
		#if name not in ('Polynomial', 'Vector', 'Matrix'):
		#	self.instances_cache = dict()
		
		#self.mutable.add('instances_cache')
		self.immutable = True
	
	def __getattr__(self, key):
		if key.startswith('algebra_') or key.startswith('_'):
			return super().__getattribute__(key)
		
		try:
			return self.algebra_kwparams[key]
		except KeyError:
			pass
		
		try:
			attr = getattr(self.algebra_init, key)
			if callable(attr):
				return lambda *args, **kwargs: attr(*(args + self.algebra_params), **dict(chain(self.algebra_kwparams.items(), kwargs.items())))
			else:
				return attr
		except AttributeError:
			pass
		
		raise AttributeError("Attribute not found: `{}`. Available: {}".format(key, list(chain(self.algebra_init.algebra_kwparams_names, dir(self.algebra_init)))))
	
	def __call__(self, *args, **kwargs):
		return self.algebra_init(*(args + self.algebra_params), **dict(chain(self.algebra_kwparams.items(), kwargs.items())))
	
	def __hash__(self):
		try:
			return self.hash_cache
		except AttributeError:
			hash_cache = hash((self.algebra_name, self.algebra_params, frozenset(self.algebra_kwparams.items())))
			self.hash_cache = hash_cache
			return hash_cache
	
	def __eq__(self, other):
		if self is other:
			return True
		
		try:
			self.hash_cache == other.hash_cache
		except AttributeError:
			pass
		
		try:
			return self.algebra_name == other.algebra_name and self.algebra_params == other.algebra_params and self.algebra_kwparams == other.algebra_kwparams
		except AttributeError:
			return NotImplemented
	
	def __getnewargs__(self):
		"Pickle protocol. Return the arguments for the __new__ method upon unpickling."
		return self.algebra_name, self.algebra_init.__qualname__, self.algebra_params, self.algebra_kwparams
	
	def __repr__(self):
		return 'Algebra(' + ', '.join(repr(_x) for _x in self.__getnewargs__()) + ')'
	
	def __str__(self):
		return self.algebra_name + '(' + ', '.join(self.algebra_params) + (', ' if self.algebra_params and self.algebra_kwparams else '') + ', '.join((_k + '=' + str(_v)) for (_k, _v) in self.algebra_kwparams.items()) + ')'
	
	def bit_arithmetics(self):
		"How many bits is needed to perform arithmetics in this algebra."
		
		try:
			bits = self.exponent
		except AttributeError:
			bits = (self.base_ring.size - 1).bit_length()
		
		if self.base_ring.algebra_name != 'BooleanRing':
			bits *= 2
		
		return bits



class AlgebraicStructure:
	"An object representing a concrete value. Objects of this class belong to some algebra."
	
	algebras = {}
	algebra_params_count = 0
	algebra_kwparams_names = ()
	algebra_class = Algebra
	
	def __init__(self, *args, **kwargs):
		try:
			algebra = args[0].algebra
		except (AttributeError, IndexError):
			algebra = self.get_algebra(*args, **kwargs)
		self.algebra = algebra
	
	@classmethod
	def get_algebra(cls, *params, **kwparams):
		if cls is AlgebraicStructure:
			raise RuntimeError("You should call this method only from derived class.")
		
		params = params[len(params)-cls.algebra_params_count:]
		kwparams = dict((_k, _v) for (_k, _v) in kwparams.items() if (_k in cls.algebra_kwparams_names))
		
		dictkeys = tuple(sorted(kwparams.keys()))
		dictvalues = tuple(kwparams[_key] for _key in dictkeys)
		key = (cls.__name__, params[:cls.algebra_params_count], dictkeys, dictvalues)
		try:
			algebra = cls.algebras[key]
		except KeyError:
			algebra = cls.algebras[key] = cls.algebra_class(key[0], cls, key[1], dict(zip(key[2], key[3])))
		return algebra
	
	def variables(self):
		yield from []

