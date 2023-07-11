#!/usr/bin/python3


class Array:
	def __init__(self, Field, storage, start=None, stop=None, step=None):
		self.Field = Field
		self.storage = storage
		self.start = start if start is not None else 0
		self.stop = stop if stop is not None else len(storage)
		self.step = step if step is not None else 1
	
	def __len__(self):
		return self.stop
	
	def __getitem__(self, index):
		try:
			start, stop, step = index.start, index.stop, index.step
		except AttributeError:
			pass
		else:
			return self.__class__(self.Field, self, start, stop, step)
		
		try:
			eff_index = self.start + self.step * index
		except TypeError:
			pass
		else:
			if eff_index < 0:
				eff_index = len(self) - eff_index
			if eff_index >= len(self):
				raise IndexError
			return self.Field(self.storage[eff_index])
		
		if index == Ellipsis:
			return self
		
		raise IndexError(f"Unsupported index type: {index}.")
	
	def __setitem__(self, index, value):
		try:
			start, stop, step = index.start, index.stop, index.step
		except AttributeError:
			pass
		else:
			self.__class__(self.Field, self, start, stop, step)[...] = value
			return
		
		try:
			eff_index = self.start + self.step * index
		except TypeError:
			pass
		else:
			if eff_index < 0:
				eff_index = len(self) - eff_index
			if eff_index >= len(self):
				raise IndexError
			self.storage[eff_index] = int(value)
			return
		
		if index == Ellipsis:
			for n, v in enumerate(value):
				self[n] = int(v)
			return
		
		raise IndexError(f"Unsupported index type: {index}.")


