#!/usr/bin/python3
#-*- coding:utf-8 -*-


class ExpressionOps(type):
	op_methods = ['__not__', '__add__', '__sub__', '__mul__', '__rmul__', '__pow__', '__mod__', '__neg__', '__eq__', '__lt__', '__gt__', '__le__', '__ge__', '__invert__']
	
	def __new__(cls, name, bases, classdict):
		for op_method in cls.op_methods:
			classdict[op_method] = (lambda op_m: (lambda self, *others: Expression(op_m, (self,) + others)))(op_method)
		return type.__new__(cls, name, bases, classdict)


class TracerException(BaseException):
	pass


class Expression(metaclass=ExpressionOps):
	collection_len_limit = 8
	
	def __init__(self, operator, operands=None):
		self.operator = operator
		self.operands = tuple(tuple(_operand) if isinstance(_operand, list) else _operand for _operand in operands) if (operands != None) else operands
	
	def __call__(self, *args, **kwargs):
		#print("call", args, kwargs)
		return Expression('__call__', [self, args, tuple(sorted(kwargs.items()))])
	
	def __getattr__(self, attr):
		if attr.startswith('__'):
			raise AttributeError(f"No attribute: {attr}")
		#print("getattr", attr)
		return Expression('__getattr__', [self, attr])
	
	def __len__(self):
		len_expr = Expression('__len__', [self])
		for n in range(self.collection_len_limit):
			if n < len_expr:
				continue
			if n == len_expr:
				return n
	
	def __getitem__(self, value):
		if value < Expression('__len__', [self]):
			return Expression('__getitem__', [self, value])
		else:
			raise IndexError("Index outside allowed range")
	
	def __iter__(self):
		if current_theory == None:
			yield Expression(str(self) + "...")
		else:
			n = 0
			while n < Expression('__len__', [self]):
				if n >= self.collection_len_limit:
					raise ValueError("Collection too long.")
				yield self[n]
				n += 1
	
	def __hash__(self):
		return 0
		#global current_theory
		#if current_theory == None:
		#	return 0
		#raise TypeError("Expression not hashable while evaluating")
	
	def __bool__(self):
		#print("bool", str(WrappedExpression(self)))
		global current_theory
		if current_theory == None:
			return False
		return current_theory.prove(self)
	
	def __str__(self):
		if current_theory == None:
			return str(WrappedExpression(self))
		else:
			raise TracerException(TypeError("Expression not stringable"))
	
	def __repr__(self):
		#if current_theory == None:
		return self.__class__.__name__ + '("' + str(WrappedExpression(self)) + '")'
		#else:
		#	raise TracerException(TypeError("Expression not stringable"))


def negate(x):
	try:
		if x.operator == '__negate__' and len(x.operands) == 1:
			return x.operands[0]
	except AttributeError:
		pass
	
	return Expression('__negate__', (x,))


class WrappedExpression:
	def __init__(self, expression):
		self.expression = expression
	
	def __str__(self):
		if isinstance(self.expression, Expression):
			if self.expression.operands == None:
				return chr(0x303) + self.expression.operator

			operator = self.expression.operator
			operands = self.expression.operands
			
			if operator == '__len__':
				return 'len(' + str(self.__class__(operands[0])) + ')'
			elif operator == '__getitem__':
				return str(self.__class__(operands[0])) + '[' + str(self.__class__(operands[1])) + ']'
			elif operator == '__getattr__':
				return str(self.__class__(operands[0])) + '.' + operands[1]
			elif operator == '__call__':
				if not operands[1] and not operands[2]:
					return str(self.__class__(operands[0])) + '()'
				else:
					return str(self.__class__(operands[0])) + '(*(' + str(self.__class__(operands[1])) + '), **dict(' + str(self.__class__(operands[2])) + '))'
			else:
				return ''.join((str(self.expression.operator), '(', ', '.join(str(self.__class__(_op)) for _op in self.expression.operands), ')'))
		else:
			return repr(self.expression)
	
	def __eq__(self, other):
		try:
			return self.expression.operator == other.expression.operator and \
			       (self.expression.operands == None or \
			       (len(self.expression.operands) == len(other.expression.operands) and \
			       all((self.__class__(_x) == self.__class__(_y)) for (_x, _y) in zip(self.expression.operands, other.expression.operands))))
		except (AttributeError, TypeError):
			pass
		
		if not hasattr(self.expression, 'operator') and (not hasattr(other, 'expression') or not hasattr(other.expression, 'operator')):
			return self.expression == other
		
		return NotImplemented
	
	def __hash__(self):
		try:
			#return hash(tuple([5321, self.expression.operator] + [hash(self.__class__(_op)) for _op in self.expression.operands] if self.expression.operands != None else [289374]))
			return hash(tuple([5321, self.expression.operator] + [len(self.expression.operands)] if self.expression.operands != None else [289374]))
		except (AttributeError, TypeError):
			return hash(self.expression)
	
	def __le__(self, other):
		return str(self) < str(other)
	
	def negate(self):
		return self.__class__(negate(self.expression))
	
	def evaluate(self, _model, **kwargs):
		try:
			operator = self.expression.operator
		except AttributeError:
			return self.expression
		
		operands = self.expression.operands
		
		if operands == None:
			return kwargs[operator]
		
		if operator == '__add__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs) + self.__class__(operands[1]).evaluate(_model, **kwargs)
		elif operator == '__sub__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs) - self.__class__(operands[1]).evaluate(_model, **kwargs)
		elif operator == '__mul__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs) * self.__class__(operands[1]).evaluate(_model, **kwargs)
		elif operator == '__rmul__':
			return self.__class__(operands[1]).evaluate(_model, **kwargs) * self.__class__(operands[0]).evaluate(_model, **kwargs)
		elif operator == '__mod__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs) % self.__class__(operands[1]).evaluate(_model, **kwargs)
		elif operator == '__pow__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs) ** self.__class__(operands[1]).evaluate(_model, **kwargs)
		elif operator == '__eq__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs) == self.__class__(operands[1]).evaluate(_model, **kwargs)
		elif operator == '__ge__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs) >= self.__class__(operands[1]).evaluate(_model, **kwargs)
		elif operator == '__gt__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs) > self.__class__(operands[1]).evaluate(_model, **kwargs)
		elif operator == '__invert__':
			return ~self.__class__(operands[0]).evaluate(_model, **kwargs)
		elif operator == '__neg__':
			return -self.__class__(operands[0]).evaluate(_model, **kwargs)
		elif operator == '__negate__':
			return not self.__class__(operands[0]).evaluate(_model, **kwargs)
		
		elif operator == '__len__':
			return len(self.__class__(operands[0]).evaluate(_model, **kwargs))
		elif operator == '__getitem__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs)[self.__class__(operands[1]).evaluate(_model, **kwargs)]
		elif operator == '__getattr__':
			return getattr(self.__class__(operands[0]).evaluate(_model, **kwargs), self.__class__(operands[1]).evaluate(_model, **kwargs))
		elif operator == '__call__':
			return self.__class__(operands[0]).evaluate(_model, **kwargs)(*self.__class__(operands[1]).evaluate(_model, **kwargs), **dict(self.__class__(operands[2]).evaluate(_model, **kwargs)))
		
		else:
			return getattr(_model, operator)(*[self.__class__(_op).evaluate(_model, **kwargs) for _op in operands])
	
	def symbols(self):
		try:
			if self.expression.operator[0] != '_' and self.expression.operands != None:
				yield self.expression.operator
			elif self.expression.operands:
				for operand in self.expression.operands:
					yield from self.__class__(operand).symbols()
		except AttributeError:
			pass
	
	def variables(self):
		try:
			if self.expression.operator[0] != '_' and self.expression.operands == None:
				yield self.expression.operator
			elif self.expression.operands:
				for operand in self.expression.operands:
					yield from self.__class__(operand).symbols()
		except AttributeError:
			pass


class Theory:
	def __init__(self, axiom=None, parent=None):
		#self.axiom = WrappedExpression(axiom)
		#self.parent = parent
		
		w_axiom = WrappedExpression(axiom)
		if parent and w_axiom != None:
			self.__axiom_set = parent.axiom_set() | frozenset([w_axiom])
		elif parent:
			self.__axiom_set = parent.axiom_set()
		elif w_axiom != None:
			self.__axiom_set = frozenset([w_axiom])
		else:
			self.__axiom_set = frozenset()
	
	def axioms(self):
		#if self.axiom != None:
		#	yield self.axiom
		#
		#if self.parent:
		#	yield from self.parent.axioms()
		yield from self.__axiom_set
	
	def axiom_set(self):
		return self.__axiom_set
		#try:
		#	return self.saved_axiom_set
		#except AttributeError:
		#	pass
		#
		#if self.axiom != None and self.parent:
		#	self.saved_axiom_set = self.parent.axiom_set() | frozenset([self.axiom])
		#elif self.axiom != None:
		#	self.saved_axiom_set = frozenset([self.axiom])
		#elif self.parent:
		#	self.saved_axiom_set = self.parent.axiom_set()
		#else:
		#	self.saved_axiom_set = frozenset()
		#
		#return self.saved_axiom_set
	
	def __len__(self):
		try:
			return self.saved_len
		except AttributeError:
			pass
		
		#l = 0
		#if self.parent:
		#	l += len(self.parent)
		#if self.axiom != None:
		#	l += 1
		#self.saved_len = l
		
		self.saved_len = len(self.axiom_set())
		return self.saved_len
	
	def assume(self, expression):
		return Theory(expression, self)
	
	def prove(self, expression):
		w_expression = WrappedExpression(expression)
		#print("prove... ", str(w_expression))
		try:
			if w_expression in self.axiom_set():
				#print("True", str(w_expression))
				return True
			elif w_expression.negate() in self.axiom_set():
				#print("False", str(w_expression))
				return False
			else:
				#print("IncompleteTheory", str(w_expression))
				raise IncompleteTheory(expression, self)
		except Exception as error:
			print("Error in prove:", error, str(w_expression))
			raise
	
	def consistent(self):
		return not self.prove(False)
	
	def __enter__(self):
		global current_theory
		self.previous_theory = current_theory
		current_theory = self
	
	def __exit__(self, *args):
		global current_theory
		current_theory = self.previous_theory
		del self.previous_theory
	
	def __str__(self):
		return "; ".join(str(_ax) for _ax in self.axioms())


current_theory = None


class IncompleteTheory(BaseException):
	def __init__(self, expression, theory):
		self.expression = expression
		self.theory = theory
	
	def __str__(self):
		return f"Could not prove nor disprove formula: {str(WrappedExpression(self.expression))}"


def universal(*variables):
	exprs = dict((_v, Expression(_v)) for _v in variables)
	
	def decor(original):
		def modified(**kwargs):
			kwargs = dict(kwargs)
			kwargs.update(exprs)
			return original(**kwargs)
		
		modified.__name__ = original.__name__
		modified.__qualname__ = original.__qualname__
		
		try:
			modified.universal_symbols = original.universal_symbols
		except AttributeError:
			modified.universal_symbols = {}
		
		modified.universal_symbols.update(exprs)
		
		try:
			modified.existential_symbols = original.existential_symbols
		except AttributeError:
			modified.existential_symbols = {}
		
		for name, expr in modified.existential_symbols.items():
			expr.operands = tuple(exprs[_v] for _v in variables) + expr.operands
		
		return modified
	
	return decor


def existential(*variables):
	exprs = dict((_v, Expression(_v, ())) for _v in variables)
	
	def decor(original):
		def modified(**kwargs):
			kwargs = dict(kwargs)
			kwargs.update(exprs)
			return original(**kwargs)
		
		modified.__name__ = original.__name__
		modified.__qualname__ = original.__qualname__
		
		try:
			modified.universal_symbols = original.universal_symbols
		except AttributeError:
			modified.universal_symbols = {}
		
		try:
			modified.existential_symbols = original.existential_symbols
		except AttributeError:
			modified.existential_symbols = {}
		
		modified.existential_symbols.update(exprs)
		
		return modified
	
	return decor



#def into_queue(call, queue, *args):
#	queue.put(call(*args))

class Record:
	pass




class model:
	thread_pool = 1
	search_depth_limit = 18
	original = Record()
	
	@classmethod
	def __trace_parallel(cls, queue, thread_pool, search_depth_limit, original, fn, theory):
		cls.thread_pool = thread_pool
		cls.search_depth_limit = search_depth_limit
		cls.original = original
		queue.put(cls.__trace(fn, theory))
	
	'''
	@classmethod
	def __trace(cls, fn, theory):
		try:
			with theory:
				r = fn()
			variable_assumptions = [_assumption for _assumption in theory.axioms() if not frozenset(_assumption.symbols())]
			symbol_assumptions = [_assumption for _assumption in theory.axioms() if frozenset(_assumption.symbols())]
			return [(variable_assumptions, symbol_assumptions, r)], []
		except IncompleteTheory as it:
			if len(theory) >= cls.search_depth_limit:
				return [], [(theory, RuntimeError("Search depth limit exceeded."))]
			t1, n1 = cls.__trace(fn, theory.assume(it.expression))
			t2, n2 = cls.__trace(fn, theory.assume(negate(it.expression)))
			return t1 + t2, n1 + n2
		except Exception as e:
			variable_assumptions = [_assumption for _assumption in theory.axioms() if not frozenset(_assumption.symbols())]
			symbol_assumptions = [_assumption for _assumption in theory.axioms() if frozenset(_assumption.symbols())]
			return [], [(variable_assumptions, symbol_assumptions, e)] # TODO: remove exception reason
	'''
	
	@classmethod
	def __try_theory(cls, theory, fn, search_depth_limit):
		try:
			with theory:
				r = fn()
			variable_assumptions = [_assumption for _assumption in theory.axioms() if not frozenset(_assumption.symbols())]
			symbol_assumptions = [_assumption for _assumption in theory.axioms() if frozenset(_assumption.symbols())]
			result = r
			success = True
		except IncompleteTheory as it:
			if len(theory) >= search_depth_limit:
				variable_assumptions = [_assumption for _assumption in theory.axioms() if not frozenset(_assumption.symbols())]
				symbol_assumptions = [_assumption for _assumption in theory.axioms() if frozenset(_assumption.symbols())]
				result = RuntimeError("Search depth limit exceeded.")
				success = False
			else:
				raise
		except Exception as e:
			variable_assumptions = [_assumption for _assumption in theory.axioms() if not frozenset(_assumption.symbols())]
			symbol_assumptions = [_assumption for _assumption in theory.axioms() if frozenset(_assumption.symbols())]
			result = e # TODO: remove exception reason
			success = False				
		return variable_assumptions, symbol_assumptions, result, success, theory

	@classmethod
	def __try_theory_parallel(cls, queue, condition, task_finished, theory, fn, search_depth_limit):
		#print("start", id(queue))
		try:
			variable_assumptions, symbol_assumptions, result, success, theory = cls.__try_theory(theory, fn, search_depth_limit)
			queue.put((variable_assumptions, symbol_assumptions, result, success, theory))
		except (Exception, IncompleteTheory) as error:
			queue.put((None, None, error, False, theory))
		finally:
			with condition:
				task_finished.value += 1
				#print("send", task_finished.value)
				condition.notify_all()
			queue.task_done()
		#print("end", id(queue))
	
	@classmethod
	def __trace(cls, fn):
		theories = [Theory()]
		rules = []
		forbidden = []
		while theories and len(rules) < 2345:
			print(len(theories), len(rules), len(forbidden))
			theory = theories.pop()
			try:
				variable_assumptions, symbol_assumptions, result, success, theory = cls.__try_theory(theory, fn, cls.search_depth_limit)
			except IncompleteTheory as it:
				theory = it.theory
				theories.append(theory.assume(it.expression))
				theories.append(theory.assume(negate(it.expression)))
			else:
				if success:
					rules.append((variable_assumptions, symbol_assumptions, result))
				else:
					forbidden.append((variable_assumptions, symbol_assumptions, result))
		return rules, forbidden
	
	@classmethod
	def __trace_parallel(cls, fn):
		from multiprocessing import Process, JoinableQueue, Condition, Value
		from ctypes import c_uint
		
		theories = [Theory()]
		rules = []
		forbidden = []
		
		pending = []
		condition = Condition()
		task_finished = Value(c_uint, 0)
		
		while theories or pending:
			#print(len(theories), len(pending))
			if theories:
				theory = theories.pop()
				queue = JoinableQueue()
				process = Process(target=cls.__try_theory_parallel, args=(queue, condition, task_finished, theory, fn, cls.search_depth_limit))
				process.start()
				pending.append(queue)
			elif pending:
				#print(pending)
				with condition:
					if not task_finished.value:
						condition.wait_for(lambda: task_finished.value)
						#print("recv", task_finished.value)
						task_finished.value -= 1
			
			for queue in pending:
				if queue.empty():
					continue
				
				try:
					variable_assumptions, symbol_assumptions, result, success, theory = queue.get()
					if variable_assumptions == symbol_assumptions == None and not success:
						raise result
				except IncompleteTheory as it:
					theory = it.theory
					theories.append(theory.assume(it.expression))
					theories.append(theory.assume(negate(it.expression)))
				else:
					if success:
						rules.append((variable_assumptions, symbol_assumptions, result))
					else:
						forbidden.append((variable_assumptions, symbol_assumptions, result))
				
				queue.join()
				pending.remove(queue)
		
		return rules, forbidden
	
	def __init__(self, fn):
		setattr(self.__class__.original, fn.__name__, fn)
		globals()[fn.__name__] = self
		fn.__qualname__ = self.__class__.__qualname__ + '.original.' + fn.__name__
		
		self.__name__ = fn.__name__
		self.__qualname__ = fn.__qualname__
		
		self.__kwargs = fn.universal_symbols
		
		for name, symbol in fn.existential_symbols.items():
			self.__dict__[name] = lambda *args: Expression(symbol.operator, args)
		
		self.__rules, self.__forbidden = self.__trace(fn)
		
		for name, symbol in fn.existential_symbols.items():
			self.__dict__[name] = (lambda _name: (lambda *args: self.__symbol(_name, *args)))(name)
	
	def __symbol(self, name, *args):
		if self.__name__ == 'factorial' and name == 'y':
			x = args[0]
			if x == 0 or x == 1:
				return 1
			else:
				r = 1
				for n in range(1, x + 1):
					r *= n
				return r
		return 0
	
	def __call__(self, **kwargs):
		if frozenset(kwargs.keys()) != frozenset(self.__kwargs.keys()):
			raise TypeError("Allowed keyword arguments are: " + ", ".join(self.__kwargs.keys()))
		
		for variable_assumptions, symbol_assumptions, result in self.__rules:
			if all(_axiom.evaluate(self, **kwargs) for _axiom in variable_assumptions):
				return WrappedExpression(result).evaluate(self, **kwargs)
		
		for variable_assumptions, symbol_assumptions, error in self.__forbidden:
			if all(_axiom.evaluate(self, **kwargs) for _axiom in variable_assumptions):
				raise WrappedExpression(error).evaluate(self, **kwargs)
		
		raise TypeError("The arguments provided do not match the declared function types.")



def dump_model(m):
	from collections import Counter
	results = Counter()
	for tv, ts, r in m._model__rules:
		result = str(WrappedExpression(r))
		results[result] += 1
		print([str(_t) for _t in tv], "=>", [str(_t) for _t in ts], result)
	print(len(m._model__rules))
	for result, freq in results.most_common():
		print(" ", freq, ":", result)
	print(len(results))
	#for tv, ts, e in m._model__forbidden:
	#	print([str(_t) for _t in tv], "=> !", [str(_t) for _t in ts], repr(e))
	#print(len(m._model__forbidden))


if __name__ == '__main__':
	from term import Term
	from polynomial import Polynomial
	from rings import BooleanRing
	
	polynomial = Polynomial.get_algebra(base_ring=BooleanRing.get_algebra())
	
	
	@model
	@universal('x')
	def trace(x):
		#return polynomial(x).evaluate_constants()
		#return polynomial(x).evaluate_repetitions()
		#return polynomial(x).order()
		#return polynomial(x).extract()
		#return polynomial(x).circuit_size()
		return polynomial(x).additive_form()
		#return polynomial(x).optimized()
	
	#dump_model(trace)
	
	pr = polynomial.random('abcdefgh', order=4)
	
	for tv, ts, result in trace._model__rules:
		if all([_t.evaluate(trace, x=pr) for _t in tv]):
			print(repr(result))
	
	
	#polynomial = Polynomial.get_algebra(base_ring=BooleanRing.get_algebra())
	
	#p1 = polynomial.random(variables='abcdefgh', order=4)
	
	#print(p1)




