#!/usr/bin/python3
#-*- coding:utf8 -*-

"Utility functions."

from itertools import starmap
from multiprocessing import current_process, cpu_count
from multiprocessing.pool import Pool


__all__ = 'randbelow', 'parallel', 'parallel_map', 'parallel_starmap', 'random_sample', 'random_permutation', 'Immutable', 'memoize', 'canonical', 'optimized', 'evaluate', 'substitute', 'valuations'


if __debug__:
	from random import randrange
	
	def randbelow(modulus):
		"In debug mode, use pseudo-random number generator."
		return randrange(modulus)
else:
	from secrets import randbelow
	"In release mode, use system entropy source."


def canonical(x):
	return x.canonical()


def optimized(x):
	return x.optimized()


def evaluate(x):
	return x.evaluate()


def substitute(x, algebra, subst):
	#print("substitute")
	if hasattr(x, 'operator'):
		return x(**subst)
	else:
		return algebra.const(x)


def valuations(*variable):
	for valuation in product(*[_v.algebra.base_ring.domain() for _v in variable]):
		yield dict(zip((str(_v) for _v in variable), valuation))


def memoize(function):
	cache = dict()
	
	def memoized(*args, **kwargs):
		kwkey = tuple((_k, kwargs[_k]) for _k in sorted(kwargs.keys()))
		try:
			return cache[args, kwkey]
		except KeyError:
			result = function(*args, **kwargs)
			cache[args, kwkey] = result
			return result
	
	memoized.__name__ = function.__name__
	return memoized


parallelism = 0


class parallel:
	def __init__(self, p=cpu_count()):
		self.new_parallelism = p
	
	def __enter__(self):
		global parallelism
		self.old_parallelism = parallelism
		parallelism = self.new_parallelism
		return self
	
	def __exit__(self, *args):
		global parallelism
		parallelism = self.old_parallelism


def parallel_map(fun, iterable):
	if parallelism and not current_process().daemon:
		with Pool(parallelism) as p:
			return p.map(fun, iterable)
	else:
		return map(fun, iterable)


def parallel_starmap(fun, iterable):
	if parallelism and not current_process().daemon:
		with Pool(parallelism) as p:
			return p.starmap(fun, iterable)
	else:
		return starmap(fun, iterable)


def random_permutation(length):
	items = list(range(length))
	while items:
		yield items.pop(randbelow(len(items)))


def random_sample(iterable, length, size):
	"""
	Return a random sub-iterable of size `size` from the `iterable` of the length `length`.
	`size` must not be greater than `length`. It is an error if the `iterable` is shorter than `length`.
	"""
	
	if not size:
		return
	
	s = 0
	for n in range(size):
		mean = (length - s) // (size - n)
		for m in range(randbelow(mean)):
			next(iterable)
			s += 1
		yield next(iterable)
		s += 1
	# FIXME: sometimes ends prematurely


class Immutable:
	"Makes the object immutable. You must set `self.immutable = True` after initialization in the constructor."
	
	@property
	def immutable(self):
		try:
			return self.__immutable
		except AttributeError:
			return False
	
	@immutable.setter
	def immutable(self, value):
		object.__setattr__(self, '_Immutable__immutable', value)
	
	@property
	def mutable(self):
		try:
			return self.__mutable
		except AttributeError:
			mutable = set()
			object.__setattr__(self, '_Immutable__mutable', mutable)
			return mutable
	
	@mutable.setter
	def mutable(self, value):
		object.__setattr__(self, '_Immutable__mutable', value)
	
	def __setattr__(self, attr, value):
		if self.immutable and (attr not in self.mutable):
			raise TypeError("Immutable object.")
		else:
			object.__setattr__(self, attr, value)
	
	def __delattr__(self, attr):
		if self.immutable and (attr not in self.mutable):
			raise TypeError("Immutable object.")
		else:
			object.__delattr__(self, attr)
	
	def __hash__(self):
		if not self.immutable:
			raise TypeError("Mutable object. ({})".format(type(self)))
		return NotImplemented

