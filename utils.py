#!/usr/bin/python3


__all__ = 'subscript', 'superscript', 'cached', 'array_fallback', 'table_fallback', 'classproperty', 'FieldType', 'ArrayType', 'TableType', 'SpecialError', 'SpecialValueError', 'SpecialTypeError', 'SpecialIndexError', 'SpecialKeyError'


from typing import TypeVar
from collections import namedtuple


FieldType = TypeVar('FieldType')
ArrayType = namedtuple('ArrayType', ['sizes', 'types'])
TableType = namedtuple('TableType', ['key_sizes', 'value_sizes', 'types'])


class SpecialError(Exception):
	pass


class SpecialValueError(ValueError, SpecialError):
	pass


class SpecialTypeError(TypeError, SpecialError):
	pass


class SpecialIndexError(IndexError, SpecialError):
	pass


class SpecialKeyError(KeyError, SpecialError):
	pass


subscripts = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")

def subscript(n):
	if not n >= 0: raise ValueError("Argument can not be negative.")
	return str(n).translate(subscripts)


superscripts = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")

def superscript(n):
	if not n >= 0: raise ValueError("Argument can not be negative.")
	return str(n).translate(superscripts)


def cached(old_method):
	name = '_cached_' + old_method.__name__
	
	def new_method(self, *args):
		try:
			value = getattr(self, name)[args]
			#print(f"cache hit: {old_method.__qualname__} @{id(self)} {args}")
			return value
		except AttributeError:
			#print(f"cache miss: {old_method.__qualname__} @{id(self)} {args}")
			value = old_method(self, *args)
			store = {args: value}
			setattr(self, name, store)
			return value
		except KeyError:
			#print(f"cache miss: {old_method.__qualname__} @{id(self)} {args}")
			value = old_method(self, *args)
			getattr(self, name)[args] = value
			return value
	
	new_method.__name__ = old_method.__name__
	new_method.__qualname__ = old_method.__qualname__
	return new_method


def array_fallback(Array):
	try:
		return Array.Array
	except AttributeError:
		if isinstance(Array, type):
			return lambda values, sizes, types: Array(values)
		else:
			return Array


def table_fallback(Table):
	try:
		return Table.Table
	except AttributeError:
		return lambda items, sizes, types, Array: Table(items)


def singleton(symbol):
	return symbol()


class classproperty(property):
	def __get__(self, owner_self, owner_cls):
		return self.fget(owner_cls)

