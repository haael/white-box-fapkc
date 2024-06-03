#!/usr/bin/python3


__all__ = 'subscript', 'superscript', 'cached', 'array_fallback', 'table_fallback'


subscripts = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")

def subscript(n):
	if not n >= 0: raise ValueError
	return str(n).translate(subscripts)


superscripts = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")

def superscript(n):
	if not n >= 0: raise ValueError
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
		return lambda items, ksize, sizes, types, Array: Table(items)


'''
def sm_range(*args):
	if len(args) == 1 and hasattr(args[0], 'sm_range'):
		return args[0].sm_range()
	else:
		return range(*args)


def sm_len(a):
	if hasattr(a, 'sm_length'):
		return a.sm_length()
	else:
		return len(a)
'''

