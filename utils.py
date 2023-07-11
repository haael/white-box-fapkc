#!/usr/bin/python3


__all__ = 'subscript', 'superscript', 'cached'


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
	
	def new_method(self):
		try:
			return getattr(self, name)
		except AttributeError:
			value = old_method(self)
			setattr(self, name, value)
			return value
	
	return new_method

