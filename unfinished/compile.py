#!/usr/bin/python3



from collections import namedtuple
import dis


def a(x):
	if x < 5:
		x += 1
	
	if x > 3:
		x *= 2
	else:
		x *= x
	
	t = [2, 3, x]
	
	return b(x, 3, t) + 1


def b(y, z, t):
	k = y + z
	t[k % 3] += 1
	
	for n in range(5):
		k += t[(k + 1) % 3]
	
	for m in c(4):
		k -= m
	
	return y - y * z - 1 + k + t[0]


def c(n):
	yield n + 1
	yield n
	yield n - 1


def d(n):
	k = 1
	for m in c(n):
		k += m
	for m in range(n):
		k += m
	return k


def e(x):
	k = x
	g = k + 1
	g += d(x)
	return g + k


class Interpreter:
	def __init__(self, fun):
		self.name = fun.__name__
		self.argcount = fun.__code__.co_argcount
		self.varnames = fun.__code__.co_varnames
		self.bytecode = list(dis.Bytecode(fun))
		#print(self.name, [(_instr.opname, _instr.argval) for _instr in self.bytecode])
		self.globals_ = dict(globals())
		self.globals_.update(__builtins__.__dict__)
		self.subcall = None
	
	def set_args(self, args):
		if len(args) != self.argcount:
			raise TypeError(f"Expected {self.argcount} arguments.")
		self.args = args
	
	def enter_frame(self):
		self.locals_ = dict(zip(self.varnames[:self.argcount], self.args))
		self.stack = []
		self.position = self.bytecode[0].offset
	
	def leave_frame(self):
		del self.locals_
		del self.stack
		del self.position
	
	def is_running(self):
		return hasattr(self, 'position')
	
	def __call__(self, *args):
		self.set_args(args)
		with self:
			for pos in self:
				pass
				#print(self.stack, self.locals_)
		del self.args
		return self.result
	
	def __enter__(self):
		self.enter_frame()
		return self
	
	def __exit__(self, *args):
		self.leave_frame()
	
	def __iter__(self):
		return self
	
	def __next__(self):
		pos = self.step()
		if pos == 'return' or pos == 'generator':
			raise StopIteration
		return pos
	
	def step(self):
		if self.subcall is not None:
			pos = self.subcall.step()
			if pos == 'return':
				self.subcall.leave_frame()
				self.stack.append(self.subcall.result)
				self.subcall = None
				if hasattr(self, 'generator_exit'):
					self.stack.pop()
					self.position = self.generator_exit
					del self.generator_exit
					return self.position
			elif pos == 'generator':
				self.stack.append(self.subcall)
				self.subcall = None
			elif pos == 'yield':
				self.stack.append(self.subcall.result)
				self.subcall.stack.append(None)
				self.subcall = None
			else:
				return pos
		
		low = 0
		high = len(self.bytecode) - 1
		offset = min(self.position, high)
		
		while self.bytecode[offset].offset != self.position:
			if self.bytecode[offset].offset < self.position:
				low = offset
			elif self.bytecode[offset].offset > self.position:
				high = offset
			#print(low, offset, high, "...", self.position)
			offset = (low + high) // 2
		
		instr = self.bytecode[offset]
		#print(self.name, self.position, instr, self.stack)
		assert instr.offset == self.position
		if not hasattr(self, instr.opname):
			raise NotImplementedError(str(instr))
		pos = getattr(self, instr.opname)(instr)
		if pos is None or pos == 'return' or pos == 'generator' or pos == 'yield':
			try:
				self.position = self.bytecode[offset + 1].offset
			except IndexError:
				self.position = None
		else:
			self.position = pos
		return pos
	
	def LOAD_GLOBAL(self, instr):
		self.stack.append(self.globals_[instr.argval])
	
	def LOAD_FAST(self, instr):
		self.stack.append(self.locals_[instr.argval])
	
	def STORE_FAST(self, instr):
		self.locals_[instr.argval] = self.stack.pop()
	
	def LOAD_CONST(self, instr):
		self.stack.append(instr.argval)
	
	def BINARY_SUBTRACT(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		self.stack.append(b - a)
	
	def BINARY_ADD(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		self.stack.append(b + a)
	
	def BINARY_MULTIPLY(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		self.stack.append(b * a)
	
	def BINARY_MODULO(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		self.stack.append(b % a)
	
	def INPLACE_ADD(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		b += a
		self.stack.append(b)
	
	def INPLACE_SUBTRACT(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		b -= a
		self.stack.append(b)
	
	def INPLACE_MULTIPLY(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		b *= a
		self.stack.append(b)
	
	def COMPARE_OP(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		if instr.argval == '<':
			self.stack.append(b < a)
		elif instr.argval == '>':
			self.stack.append(b > a)
		else:
			raise NotImplementedError(str(instr))
	
	def IS_OP(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		self.stack.append(b is a)
	
	def BUILD_LIST(self, instr):
		l = self.stack[-instr.argval:]
		del self.stack[-instr.argval:]
		self.stack.append(l)
	
	def RETURN_VALUE(self, instr):
		self.result = self.stack.pop()
		return 'return'
	
	def CALL_FUNCTION(self, instr):
		if instr.argval:
			args = self.stack[-instr.argval:]
			del self.stack[-instr.argval:]
		else:
			args = []
		fun = self.stack.pop()
		
		if not hasattr(fun, '__code__'):
			self.stack.append(fun(*args))
		else:
			self.subcall = self.__class__(fun)
			self.subcall.set_args(args)
			self.subcall.enter_frame()
	
	def GEN_START(self, instr):
		return 'generator'
	
	def GET_ITER(self, instr):
		if not isinstance(self.stack[-1], Interpreter):
			self.stack.append(iter(self.stack.pop()))
	
	def FOR_ITER(self, instr):
		if not isinstance(self.stack[-1], Interpreter):
			try:
				value = next(self.stack[-1])
			except StopIteration:
				self.stack.pop()
				return instr.argval
			else:
				self.stack.append(value)
		else:
			assert self.subcall is None
			self.subcall = self.stack[-1]
			self.generator_exit = instr.argval
	
	def YIELD_VALUE(self, instr):
		self.result = self.stack.pop()
		return 'yield'
	
	def JUMP_ABSOLUTE(self, instr):
		return instr.argval
	
	def JUMP_FORWARD(self, instr):
		return instr.argval
	
	def POP_JUMP_IF_FALSE(self, instr):
		a = self.stack.pop()
		if not a:
			return instr.argval
	
	def POP_TOP(self, instr):
		self.stack.pop()
	
	def DUP_TOP_TWO(self, instr):
		stack = self.stack
		stack.append(stack[-2])
		stack.append(stack[-2])
	
	def ROT_TWO(self, instr):
		stack = self.stack
		stack[-2], stack[-1] = stack[-1], stack[-2]
	
	def ROT_THREE(self, instr):
		stack = self.stack
		stack[-3], stack[-1], stack[-2] = stack[-1], stack[-2], stack[-3]
	
	def ROT_FOUR(self, instr):
		stack = self.stack
		stack[-4], stack[-1], stack[-2], stack[-3] = stack[-1], stack[-2], stack[-3], stack[-4]
	
	def BINARY_SUBSCR(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		self.stack.append(b[a])
	
	def STORE_SUBSCR(self, instr):
		a = self.stack.pop()
		b = self.stack.pop()
		c = self.stack.pop()
		b[a] = c
	

	




interpret = Interpreter(a)

for n in range(-10, 20):
	assert interpret(n) == a(n)

quit()




InterpretLater = namedtuple('InterpretLater', 'fun variables stack skip')


class Interpreter:
	def __init__(self, main):
		self.globals_ = dict(globals())
		self.globals_.update(__builtins__.__dict__)
		self.main = main
	
	def __call__(self, *args):
		fun_variables = self.create_locals_dict()
		for n in range(self.main.__code__.co_argcount):
			fun_variables[self.main.__code__.co_varnames[n]] = args[n]
		return self.run(self.main, fun_variables)
	
	def create_locals_dict(self):
		return {}
	
	def run(self, fun, variables, stack=None, skip=0):
		print("running", fun.__name__)
		
		if stack is None:
			stack = []
		
		for instr in dis.Bytecode(fun):
			if instr.offset < skip:
				continue
			
			print(instr.opname, instr.argval)
			
			if not hasattr(self, instr.opname):
				raise NotImplementedError(str(instr))
			result = getattr(self, instr.opname)(instr, stack, variables)
			
			if result is not None:
				cmd, val = result
				if cmd == 'return':
					assert not stack
					return val
				elif cmd == 'jump':
					return self.run(fun, variables, stack, val)
				elif cmd == 'later':
					return InterpretLater(fun, variables, stack, val)
				else:
					raise NotImplementedError
		else:
			raise RuntimeError("Missing return statement.")
	
	def LOAD_GLOBAL(self, instr, stack, variables):
		stack.append(self.globals_[instr.argval])
	
	def LOAD_FAST(self, instr, stack, variables):
		stack.append(variables[instr.argval])
	
	def STORE_FAST(self, instr, stack, variables):
		variables[instr.argval] = stack.pop()
	
	def LOAD_CONST(self, instr, stack, variables):
		stack.append(instr.argval)
	
	def BINARY_SUBTRACT(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		stack.append(b - a)
	
	def BINARY_ADD(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		stack.append(b + a)
	
	def BINARY_MULTIPLY(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		stack.append(b * a)
	
	def BINARY_MODULO(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		stack.append(b % a)
	
	def INPLACE_ADD(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		b += a
		stack.append(b)
	
	def INPLACE_SUBTRACT(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		b -= a
		stack.append(b)
	
	def INPLACE_MULTIPLY(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		b *= a
		stack.append(b)
	
	def COMPARE_OP(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		if instr.argval == '<':
			stack.append(b < a)
		elif instr.argval == '>':
			stack.append(b > a)
		else:
			raise NotImplementedError(str(instr))
	
	def BUILD_LIST(self, instr, stack, variables):
		l = stack[-instr.argval:]
		del stack[-instr.argval:]
		stack.append(l)
	
	def CALL_FUNCTION(self, instr, stack, variables):
		args = stack[-instr.argval:]
		del stack[-instr.argval:]
		new_fun = stack.pop()
		
		if hasattr(new_fun, '__code__'):
			fun_variables = self.create_locals_dict()
			for n in range(new_fun.__code__.co_argcount):
				fun_variables[new_fun.__code__.co_varnames[n]] = args[n]
			result = self.run(new_fun, fun_variables)
		else:
			result = new_fun(*args)
		stack.append(result)
	
	def RETURN_VALUE(self, instr, stack, variables):
		return 'return', stack.pop()
	
	def GEN_START(self, instr, stack, variables):
		return 'later', 1
	
	def JUMP_FORWARD(self, instr, stack, variables):
		return 'jump', instr.argval
	
	def JUMP_ABSOLUTE(self, instr, stack, variables):
		return 'jump', instr.argval
	
	def POP_JUMP_IF_FALSE(self, instr, stack, variables):
		a = stack.pop()
		if not a:
			return 'jump', instr.argval
	
	def DUP_TOP_TWO(self, instr, stack, variables):
		stack.append(stack[-2])
		stack.append(stack[-2])
	
	def BINARY_SUBSCR(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		stack.append(b[a])
	
	def STORE_SUBSCR(self, instr, stack, variables):
		a = stack.pop()
		b = stack.pop()
		c = stack.pop()
		b[a] = c
	
	def ROT_TWO(self, instr, stack, variables):
		stack[-2], stack[-1] = stack[-1], stack[-2]
	
	def ROT_THREE(self, instr, stack, variables):
		stack[-3], stack[-1], stack[-2] = stack[-1], stack[-2], stack[-3]
	
	def ROT_FOUR(self, instr, stack, variables):
		stack[-4], stack[-1], stack[-2], stack[-3] = stack[-1], stack[-2], stack[-3], stack[-4]
	
	def GET_ITER(self, instr, stack, variables):
		if not isinstance(stack[-1], InterpretLater):
			stack.append(iter(stack.pop()))
	
	def FOR_ITER(self, instr, stack, variables):
		try:
			if isinstance(stack[-1], InterpretLater):
				code = stack[-1].fun
				vs = stack[-1].variables
				st = stack[-1].stack
				skip = stack[-1].skip
				value = self.run(code, vs, st, skip)
			else:
				value = next(stack[-1])
		except StopIteration:
			del stack[-1]
			return 'jump', instr.argval
		else:
			stack.append(value)


#interpret_a = Interpreter(a)
#
#for n in range(-10, 25):
#	assert interpret_a(n) == a(n)

interpret_d = Interpreter(d)

for n in range(-10, 25):
	assert interpret_d(n) == d(n)

quit()



from enum import Enum
#from collections import namedtuple
from ctypes import c_bool, c_int8, c_int16, c_int32, c_int64, c_uint8, c_uint16, c_uint32, c_uint64
from typing import Final, Callable
from inspect import getfullargspec, get_annotations, getsource
import ast
from bytecode import Bytecode
from bytecode.instr import Instr
import llvmlite.ir
import llvmlite.binding
#from types import SimpleNamespace


class CompiledTypeError(Exception):
	pass


class CompiledASTError(Exception):
	pass


class DuplicateNameError(Exception):
	pass


class TruthCheck(BaseException):
	pass


def eval_ast(node):
	if isinstance(node, ast.Name):
		return eval(node.id)
	elif isinstance(node, ast.Constant):
		return node.value
	elif isinstance(node, ast.BinOp):
		if isinstance(node.op, ast.Mult):
			return eval_ast(node.left) * eval_ast(node.right)
	
	raise CompiledASTError(f"Could not parse node: {ast.dump(node)}.")


def local_annotations(fun):
	source = getsource(fun)
	
	if source[0] in ' \t':
		source = 'if True:\n' + source
	
	tree = ast.parse(source)
	
	if source[0] in ' \t':
		body = tree.body[0].body[0].body[0].body
	else:
		body = tree.body[0].body[0].body
	
	for instr in body:
		if not isinstance(instr, ast.AnnAssign):
			continue
		
		yield instr.target.id, eval_ast(instr.annotation)


def ctype_to_llvm(ctype):	
	if ctype == None:
		return llvmlite.ir.VoidType(), False
	elif ctype == c_bool:
		return llvmlite.ir.IntType(1), False
	elif ctype == c_int8:
		return llvmlite.ir.IntType(8), True
	elif ctype == c_int16:
		return llvmlite.ir.IntType(16), True
	elif ctype == c_int32:
		return llvmlite.ir.IntType(32), True
	elif ctype == c_int64:
		return llvmlite.ir.IntType(64), True
	elif ctype == c_uint8:
		return llvmlite.ir.IntType(8), False
	elif ctype == c_uint16:
		return llvmlite.ir.IntType(16), False
	elif ctype == c_uint32:
		return llvmlite.ir.IntType(32), False
	elif ctype == c_uint64:
		return llvmlite.ir.IntType(64), False
	else:
		raise ValueError(f"Could not convert ctype: {ctype} to llvm.")


def convert_value(lltype, signed, value):
	assert not hasattr(value, 'load')
	
	if hasattr(value, 'opcode'):
		vvalue = value.opcode
	else:
		vvalue = value
	
	try:
		vsigned = value.signed
	except AttributeError:
		try:
			if vvalue >= 0:
				vsigned = None # compatible with signed and unsigned
			else:
				vsigned = True
		except TypeError:
			vsigned = True
	
	if vsigned is not None and vsigned != signed:
		raise CompiledTypeError("Mixing signed and unsigned arithmetics.")
	
	if not isinstance(vvalue, llvmlite.ir.Instruction) and not isinstance(vvalue, llvmlite.ir.Type) and not isinstance(vvalue, llvmlite.ir.Argument):
		if (abs(vvalue) - (1 if vvalue < 0 else 0)).bit_length() >= lltype.width:
			raise CompiledTypeError(f"Constant overflow: value {vvalue} does not fit in type type {lltype}.")
		vvalue = lltype(vvalue)
	else:
		if vvalue.type != lltype:
			raise CompiledTypeError(f"Value has wrong llvm type: {vvalue.type} (expected {lltype}).")
	
	return vvalue


class Proxy:
	def __init__(self, program):
		object.__setattr__(self, '_Proxy__program', program)
	
	def __getattr__(self, attr):
		return self.__program[attr]
	
	def __setattr__(self, attr, value):
		self.__program[attr] = value


class Program:
	size_t = llvmlite.ir.IntType(16) # type for indexing
	int_t = llvmlite.ir.IntType(64) # type for arithmetics
	
	def __new__(cls, class_or_name):
		if isinstance(class_or_name, type):
			class_ = class_or_name
			program = object.__new__(cls)
			program.__init__(class_.__name__)
			
			for name, ctype in get_annotations(class_, eval_str=True).items():
				if hasattr(ctype, '_getitem') and ctype._getitem == Final._getitem:
					program.constant(name, ctype.__args__[0])
				else:
					program.variable(name, ctype)
				
				try:
					program[name] = getattr(class_, name)
				except AttributeError:
					pass
			
			for symbol in class_.__dict__.values():
				if callable(symbol):
					program(symbol)
			
			class_._program = program
			return class_
		else:
			return object.__new__(cls)
	
	def __init__(self, name):
		self.module = llvmlite.ir.Module(name=name)
		self.block = None
		self.builder = None
		self.objects = {}
		
		self.raise_exception_fn = llvmlite.ir.Function(self.module, llvmlite.ir.FunctionType(llvmlite.ir.VoidType(), [llvmlite.ir.IntType(8)]), 'raise_exception')
	
	def variable(self, name, ctype):
		if name in self.objects:
			raise DuplicateNameError(f"Name already exists: {name}.")
		
		if hasattr(ctype, '_length_'):
			self.objects[name] = StaticArray(self, ctype._type_, ctype._length_, name, False)
		else:
			self.objects[name] = StaticVariable(self, ctype, name, False)
	
	def constant(self, name, ctype):
		if name in self.objects:
			raise DuplicateNameError(f"Name already exists: {name}.")
		
		if hasattr(ctype, '_length_'):
			self.objects[name] = StaticArray(self, ctype._type_, ctype._length_, name, True)
		else:
			self.objects[name] = StaticVariable(self, ctype, name, True)
	
	def function(self, name, argument_ctypes, return_ctype):
		function = Function(self, argument_ctypes, return_ctype, name)
		self.objects[name] = function
		return function
	
	def __getitem__(self, name):
		obj = self.objects[name]
		if hasattr(obj, 'load'):
			return obj.load()
		else:
			return obj
	
	def __setitem__(self, name, value):
		obj = self.objects[name]
		if hasattr(obj, 'store'):
			obj.store(value)
		else:
			obj[...] = value
	
	def is_building(self):
		return self.builder is not None
	
	def __call__(self, symbol):
		if isinstance(symbol, type):
			raise NotImplementedError("Compiling classes not implemented yet.")
		else:
			pyfun = symbol
			name = symbol.__name__
			fas = getfullargspec(symbol)
			annotations = get_annotations(pyfun, eval_str=True)
			argument_ctypes = [annotations[_name] for _name in fas.args if _name != 'self']
			return_ctype = annotations['return']
			
			with self.function(name, argument_ctypes, return_ctype) as llfun:
				annotated_vars = []
				for varname, ctype in local_annotations(pyfun):
					llfun.variable(varname, ctype)
					annotated_vars.append(varname)
				
				old_bytecode = Bytecode.from_code(pyfun.__code__)
				new_bytecode = Bytecode([])
				new_bytecode.argcount = old_bytecode.argcount
				new_bytecode.argnames = fas.args
				for instr in old_bytecode:
					if not hasattr(instr, 'name'):
						new_bytecode.append(instr)
					elif instr.name == 'LOAD_FAST' and instr.arg in annotated_vars:
						new_bytecode.append(Instr(name='LOAD_GLOBAL', arg='_function_symbol', location=instr.location))
						new_bytecode.append(Instr(name='LOAD_CONST', arg=instr.arg, location=instr.location))
						new_bytecode.append(Instr(name='BINARY_SUBSCR', location=instr.location))
					elif instr.name == 'STORE_FAST' and instr.arg in annotated_vars:
						new_bytecode.append(Instr(name='LOAD_GLOBAL', arg='_function_symbol', location=instr.location))
						new_bytecode.append(Instr(name='LOAD_CONST', arg=instr.arg, location=instr.location))
						new_bytecode.append(Instr(name='STORE_SUBSCR', location=instr.location))
					else:
						new_bytecode.append(instr)
				
				glob = dict(globals())
				glob['_function_symbol'] = llfun
				code = new_bytecode.to_code()
				pmfun = type(pyfun)(code, glob, name)
				
				if fas.args[0] == 'self':
					#keys = list(self.objects.keys())
					_self = Proxy(self)
					llfun.return_ = pmfun(_self, *llfun.arguments)
				else:
					llfun.return_ = pmfun(*llfun.arguments)
		
		return symbol
	
	def __repr__(self):
		return f'{self.__class__.__name__}({self.name})'
	
	def llvm_source(self):
		return str(self.module)
	
	def c_header(self):
		lines = []
		for name, value in self.objects.items():
			if hasattr(value, 'lltype'):
				if value.lltype == llvmlite.ir.VoidType():
					raise ValueError
				elif value.lltype.width == 1:
					lines.append(f"extern bool {name};")
				else:
					lines.append(f"extern {'u' if not value.signed else ''}int{value.lltype.width}_t {name};")
			elif hasattr(value, 'element_lltype'):
				if value.element_lltype == llvmlite.ir.VoidType():
					raise ValueError
				elif value.element_lltype.width == 1:
					lines.append(f"extern bool {name}[{value.length}];")
				else:
					lines.append(f"extern {'u' if not value.element_signed else ''}int{value.element_lltype.width}_t {name}[{value.length}];")
			elif hasattr(value, 'return_lltype'):
				argument_str = ", ".join(f"{'u' if not _s else ''}int{_t.width}_t" if _t.width != 1 else "bool" for (_s, _t) in zip(value.argument_signed, value.argument_lltypes))
				if value.return_lltype == llvmlite.ir.VoidType():
					lines.append(f"void {name}({argument_str});")
				elif value.return_lltype.width == 1:
					lines.append(f"bool {name}({argument_str});")
				else:
					lines.append(f"{'u' if not value.return_signed else ''}int{value.return_lltype.width}_t {name}({argument_str});")
		return "\n".join(lines)
	
	overflow_probability = 0.0001
	
	class ExceptionType(Enum):
		OVERFLOW_ADD = 1
		OVERFLOW_SUB = 2
		OVERFLOW_MUL = 3
		DOWNCAST_UU = 4
		DOWNCAST_SU = 5
		DOWNCAST_US = 6
		DOWNCAST_SS = 7
	
	def raise_exception(self, exctype):
		self.builder.call(self.raise_exception_fn, [llvmlite.ir.IntType(8)(exctype.value)])


class Value:
	def __init__(self, program, opcode, signed):
		self.program = program
		self.opcode = opcode
		self.signed = signed
	
	def __bool__(self):
		try:
			return bool(self.opcode.constant)
		except AttributeError:
			pass
		
		if not self.program.is_building():
			raise ValueError("Boolean value available only during building.")
		
		#if self.signed:
		#	cnd = self.program.builder.icmp_signed(self.opcode, 0)
		#else:
		#	cnd = self.program.builder.icmp_unsigned(self.opcode, 0)
		
		for o, v in self.program.visited_predicates:
			if o is not None:
				print(o.opcode, self.opcode, (o.opcode == self.opcode))
			if o is not None and o.opcode is self.opcode:
				return v
		else:
			raise TruthCheck(self)
	
	def cast(self, lltype, signed):
		if self.opcode.type == lltype and self.signed == signed:
			return self
		
		if self.opcode.type.width == lltype.width:
			raise NotImplementedError("Sign conversion not implemented")		
		elif self.opcode.type.width < lltype.width:
			if self.signed and signed:
				if hasattr(self.opcode, 'constant'):
					return self.__class__(self.program, lltype(self.opcode.constant), signed)
				else:
					return self.__class__(self.program, self.program.builder.sext(self.opcode, lltype), signed)
			elif not self.signed and not signed:
				if hasattr(self.opcode, 'constant'):
					return self.__class__(self.program, lltype(self.opcode.constant), signed)
				else:
					return self.__class__(self.program, self.program.builder.zext(self.opcode, lltype), signed)
			elif self.signed and not signed:
				...
				return self.__class__(self.program, self.program.builder.zext(self.opcode, lltype), signed)
			elif not self.signed and signed:
				return self.__class__(self.program, self.program.builder.sext(self.opcode, lltype), signed)
			else:
				raise RuntimeError
		elif self.opcode.type.width > lltype.width:
			if self.signed and signed:
				...
			elif not self.signed and not signed:
				...
			elif self.signed and not signed:
				...
			elif not self.signed and signed:
				...
			else:
				raise RuntimeError
			return self.__class__(self.program, self.program.builder.trunc(self.opcode, lltype), signed)
		else:
			raise RuntimeError
	
	def __add__(self, other):
		if hasattr(other, 'load'):
			other = other.load()
		if not hasattr(other, 'opcode'):
			other = self.__class__(self.program, convert_value(self.program.int_t, True, other), True)
		value = self.program.builder.sadd_with_overflow(self.cast(self.program.int_t, True).opcode, other.cast(self.program.int_t, True).opcode)
		overflow = self.program.builder.extract_value(value, 1)
		with self.program.builder.if_then(overflow, likely=self.program.overflow_probability):
			self.program.raise_exception(self.program.ExceptionType.OVERFLOW_ADD)
		result = self.program.builder.extract_value(value, 0)
		return self.__class__(self.program, result, True)
	
	def __radd__(self, other):
		if hasattr(other, 'load'):
			other = other.load()
		if not hasattr(other, 'opcode'):
			other = self.__class__(self.program, convert_value(self.program.int_t, True, other), True)
		value = self.program.builder.sadd_with_overflow(other.cast(self.program.int_t, True).opcode, self.cast(self.program.int_t, True).opcode)
		overflow = self.program.builder.extract_value(value, 1)
		with self.program.builder.if_then(overflow, likely=self.program.overflow_probability):
			self.program.raise_exception(self.program.ExceptionType.OVERFLOW_ADD)
		result = self.program.builder.extract_value(value, 0)
		return self.__class__(self.program, result, True)
	
	def __sub__(self, other):
		if hasattr(other, 'load'):
			other = other.load()
		if not hasattr(other, 'opcode'):
			other = self.__class__(self.program, convert_value(self.program.int_t, True, other), True)
		value = self.program.builder.ssub_with_overflow(self.cast(self.program.int_t, True).opcode, other.cast(self.program.int_t, True).opcode)
		overflow = self.program.builder.extract_value(value, 1)
		with self.program.builder.if_then(overflow, likely=self.program.overflow_probability):
			self.program.raise_exception(self.program.ExceptionType.OVERFLOW_SUB)
		result = self.program.builder.extract_value(value, 0)
		return self.__class__(self.program, result, True)
	
	def __rsub__(self, other):
		if hasattr(other, 'load'):
			other = other.load()
		if not hasattr(other, 'opcode'):
			other = self.__class__(self.program, convert_value(self.program.int_t, True, other), True)
		value = self.program.builder.ssub_with_overflow(other.cast(self.program.int_t, True).opcode, self.cast(self.program.int_t, True).opcode)
		overflow = self.program.builder.extract_value(value, 1)
		with self.program.builder.if_then(overflow, likely=self.program.overflow_probability):
			self.program.raise_exception(self.program.ExceptionType.OVERFLOW_SUB)
		result = self.program.builder.extract_value(value, 0)
		return self.__class__(self.program, result, True)
	
	def __mul__(self, other):
		if hasattr(other, 'load'):
			other = other.load()
		if not hasattr(other, 'opcode'):
			other = self.__class__(self.program, convert_value(self.program.int_t, True, other), True)
		value = self.program.builder.smul_with_overflow(self.cast(self.program.int_t, True).opcode, other.cast(self.program.int_t, True).opcode)
		overflow = self.program.builder.extract_value(value, 1)
		with self.program.builder.if_then(overflow, likely=self.program.overflow_probability):
			self.program.raise_exception(self.program.ExceptionType.OVERFLOW_MUL)
		result = self.program.builder.extract_value(value, 0)
		return self.__class__(self.program, result, True)
	
	def __rmul__(self, other):
		if hasattr(other, 'load'):
			other = other.load()
		if not hasattr(other, 'opcode'):
			other = self.__class__(self.program, convert_value(self.program.int_t, True, other), True)
		value = self.program.builder.smul_with_overflow(other.cast(self.program.int_t, True).opcode, self.cast(self.program.int_t, True).opcode)
		overflow = self.program.builder.extract_value(value, 1)
		with self.program.builder.if_then(overflow, likely=self.program.overflow_probability):
			self.program.raise_exception(self.program.ExceptionType.OVERFLOW_MUL)
		result = self.program.builder.extract_value(value, 0)
		return self.__class__(self.program, result, True)


class LoadValue:
	def __add__(self, other):
		return self.load() + other
	
	def __radd__(self, other):
		return other + self.load()
	
	def __sub__(self, other):
		return self.load() - other
	
	def __rsub__(self, other):
		return other - self.load()
	
	def __mul__(self, other):
		return self.load() * other
	
	def __rmul__(self, other):
		return other * self.load()


class StaticVariable(LoadValue):
	def __init__(self, program, ctype, name, constant):
		self.program = program
		self.lltype, self.signed = ctype_to_llvm(ctype)
		self.variable = llvmlite.ir.GlobalVariable(self.program.module, self.lltype, name)
		self.constant = constant
		self.variable.global_constant = constant
	
	def load(self):
		if self.program.is_building():
			return Value(self.program, self.program.builder.load(self.variable), self.signed)
		else:
			return self.variable.initializer.constant
	
	def store(self, value):
		if hasattr(value, 'load'):
			value = value.load()
		
		if self.program.is_building():
			if self.constant:
				raise ValueError("Can not modify a constant value.")
			
			if hasattr(value, 'load'):
				value = value.load()
			if not hasattr(value, 'opcode'):
				value = Value(self.program, convert_value(self.lltype, self.signed, value), self.signed)
			else:
				value = value.cast(self.lltype, self.signed)
			
			self.program.builder.store(value.opcode, self.variable)
		else:
			self.variable.initializer = llvmlite.ir.Constant(self.lltype, value)


class StaticArray:
	def __init__(self, program, ctype, length, name, constant):
		self.program = program
		self.length = length
		self.element_lltype, self.element_signed = ctype_to_llvm(ctype)
		self.array_lltype = llvmlite.ir.ArrayType(self.element_lltype, self.length)
		self.array = llvmlite.ir.GlobalVariable(self.program.module, self.array_lltype, name)
		self.constant = constant
		self.array.global_constant = constant
	
	def __len__(self):
		return self.length
	
	def __getitem__(self, index):
		if hasattr(index, 'load'):
			index = index.load()
		
		if self.program.is_building():
			if hasattr(index, 'load'):
				index = index.load()
			if not hasattr(index, 'opcode'):
				index = Value(self.program, convert_value(self.program.size_t, True, index), True)
			else:
				index = index.cast(self.program.size_t, True)
			
			address = self.program.builder.gep(self.array, [self.program.size_t(0), index.opcode])
			return Value(self.program, self.program.builder.load(address), self.element_signed)
		else:
			return self.array.initializer.constant[index].constant
	
	def __setitem__(self, index, value):
		if hasattr(value, 'load'):
			value = value.load()
		
		if index is Ellipsis and self.program.is_building():
			if self.constant:
				raise ValueError("Can not modify a constant array.")
			
			for n, v in enumerate(value):
				self[n] = v
		
		elif index is Ellipsis and not self.program.is_building():
			if not isinstance(value, bytes) and not isinstance(value, bytearray):
				initializer = [convert_value(self.element_lltype, self.element_signed, _v) for _v in value]
			else:
				initializer = value
			self.array.initializer = llvmlite.ir.Constant(self.array_lltype, initializer)
		
		elif index is not Ellipsis and self.program.is_building():
			if self.constant:
				raise ValueError("Can not modify a constant array.")
			
			if hasattr(value, 'load'):
				value = value.load()
			if not hasattr(value, 'opcode'):
				value = Value(self.program, convert_value(self.element_lltype, self.element_signed, value), self.signed)
			else:
				value = value.cast(self.element_lltype, self.element_signed)
			
			if hasattr(index, 'load'):
				index = index.load()
			if not hasattr(index, 'opcode'):
				index = Value(self.program, convert_value(self.program.size_t, True, index), True)
			else:
				index = index.cast(self.program.size_t, True)
			
			address = self.program.builder.gep(self.array, [self.program.size_t(0), index.opcode])
			self.program.builder.store(value.opcode, address)
		
		elif index is not Ellipsis and not self.program.is_building():
			self.array.initializer.constant[index] = llvmlite.ir.Constant(self.element_lltype, value)
		
		else:
			raise RuntimeError


class Function:
	def __init__(self, program, argument_ctypes, return_ctype, name):
		self.program = program
		self.argument_lltypes = [ctype_to_llvm(_ctype)[0] for _ctype in argument_ctypes]
		self.argument_signed = [ctype_to_llvm(_ctype)[1] for _ctype in argument_ctypes]
		self.return_lltype, self.return_signed = ctype_to_llvm(return_ctype)
		self.function_lltype = llvmlite.ir.FunctionType(self.return_lltype, self.argument_lltypes)
		self.function = llvmlite.ir.Function(self.program.module, self.function_lltype, name)
		self.objects = {}
	
	@property
	def return_(self):
		raise RuntimeError
	
	@return_.setter
	def return_(self, value):
		if value is None:
			if self.return_lltype != llvmlite.ir.VoidType():
				raise CompiledTypeError(f"Returning void from non-void function ({self.return_lltype}).")
			self.program.builder.ret_void()
		else:
			if hasattr(value, 'load'):
				value = value.load()
			if not hasattr(value, 'opcode'):
				value = Value(self.program, convert_value(self.return_lltype, self.return_signed, value), self.return_signed)
			else:
				value = value.cast(self.return_lltype, self.return_signed)
			
			self.program.builder.ret(value.cast(self.return_lltype, self.return_signed).opcode)
	
	@property
	def arguments(self):
		return [Value(self.program, _arg, _signed) for (_arg, _signed) in zip(self.function.args, self.argument_signed)]
	
	def __enter__(self):
		block = self.function.append_basic_block()
		self.program.builder = llvmlite.ir.IRBuilder(block)
		return self
	
	def __exit__(self, *args):
		self.program.builder = None
	
	def __call__(self, *args):
		return self.program.builder.call(self.function, [_lltype(_arg) for (_lltype, _arg) in zip(self.argument_lltypes, args)])
	
	def variable(self, name, ctype):
		if name in self.objects:
			raise DuplicateNameError(f"Name already exists: {name}.")
		
		if hasattr(ctype, '_length_'):
			self.objects[name] = DynamicArray(self.program, ctype._type_, ctype._length_)
		else:
			self.objects[name] = DynamicVariable(self.program, ctype)
	
	def __getitem__(self, name):
		obj = self.objects[name]
		if hasattr(obj, 'load'):
			return obj.load()
		else:
			return obj
	
	def __setitem__(self, name, value):
		obj = self.objects[name]
		if hasattr(obj, 'store'):
			obj.store(value)
		else:
			obj[...] = value
	
	def for_loop(self, start, stop=None, step=None):
		if stop is None and step is None:
			stop = start
			start = 0
			step = 1
		elif stop is not None and step is None:
			step = 1
		
		#if step > 0:
		#	if start > stop:
		#		raise ValueError("If step is greater than 0, start must be lesser than stop.")
		#elif step < 0:
		#	if start < stop:
		#		raise ValueError("If step is lesser than 0, start must be greater than stop.")
		#else:
		#	raise ValueError("Step must not be 0.")
		
		if hasattr(start, 'load'): start = start.load()
		if hasattr(stop, 'load'): stop = stop.load()
		if hasattr(step, 'load'): step = step.load()
		
		if not hasattr(start, 'opcode'):
			start = Value(self.program, convert_value(self.program.size_t, True, start), True)
		else:
			start = start.cast(self.program.size_t, True)
		
		if not hasattr(stop, 'opcode'):
			stop = Value(self.program, convert_value(self.program.size_t, True, stop), True)
		else:
			stop = stop.cast(self.program.size_t, True)
		
		if not hasattr(step, 'opcode'):
			step = Value(self.program, convert_value(self.program.size_t, True, step), True)
		else:
			step = step.cast(self.program.size_t, True)
		
		begin = self.program.builder.block
		loop_var_begin = start
		
		test = self.function.append_basic_block()
		self.program.builder.branch(test) # begin -> test
		self.program.builder = llvmlite.ir.IRBuilder(test)
		loop_var_test = Value(self.program, self.program.builder.phi(self.program.size_t), True)
		loop_var_test.opcode.add_incoming(loop_var_begin.opcode, begin)
		cnd = self.program.builder.icmp_signed('<', loop_var_test.opcode, stop.opcode)
		test_builder = self.program.builder
		
		body = self.function.append_basic_block()
		self.program.builder = llvmlite.ir.IRBuilder(body)		
		yield loop_var_test
		loop_var_body = (loop_var_test + step).cast(self.program.size_t, True)
		loop_var_test.opcode.add_incoming(loop_var_body.opcode, self.program.builder.block)
		
		end = self.function.append_basic_block()
		self.program.builder.branch(test) # body -> test
		self.program.builder = llvmlite.ir.IRBuilder(end)
		test_builder.cbranch(cnd, body, end) # test -> body, end


class DynamicVariable(LoadValue):
	def __init__(self, program, ctype):
		self.program = program
		self.lltype, self.signed = ctype_to_llvm(ctype)
		self.variable = self.program.builder.alloca(self.lltype)
	
	def load(self):
		assert self.program.is_building()
		
		return Value(self.program, self.program.builder.load(self.variable), self.signed)
	
	def store(self, value):
		assert self.program.is_building()
		
		if hasattr(value, 'load'):
			value = value.load()
		if not hasattr(value, 'opcode'):
			value = Value(self.program, convert_value(self.lltype, self.signed, value), self.signed)
		else:
			value = value.cast(self.lltype, self.signed)
		
		self.program.builder.store(value.opcode, self.variable)


class DynamicArray:
	def __init__(self, program, ctype, length):
		self.program = program
		self.element_lltype, self.element_signed = ctype_to_llvm(ctype)
		self.length = length
		self.array_lltype = llvmlite.ir.ArrayType(self.element_lltype, self.length)
		self.array = self.program.builder.alloca(self.element_lltype, length)
	
	def __len__(self):
		return self.length
	
	def __getitem__(self, index):
		assert self.program.is_building()
		
		if hasattr(index, 'load'):
			index = index.load()
		if not hasattr(index, 'opcode'):
			index = Value(self.program, convert_value(self.program.size_t, True, index), True)
		else:
			index = value.cast(self.program.size_t, True)
		
		address = self.program.builder.gep(self.array, [index.opcode])
		return Value(self.program, self.program.builder.load(address), self.element_signed)
	
	def __setitem__(self, index, value):
		assert self.program.is_building()
		
		if index is Ellipsis:
			for n, v in enumerate(value):
				self[n] = v
		else:
			if hasattr(value, 'load'):
				value = value.load()
			if not hasattr(value, 'opcode'):
				value = Value(self.program, convert_value(self.element_lltype, self.element_signed, value), self.element_signed)
			else:
				value = value.cast(self.element_lltype, True)
			
			if hasattr(index, 'load'):
				index = index.load()
			if not hasattr(index, 'opcode'):
				index = Value(self.program, convert_value(self.program.size_t, True, index), True)
			else:
				index = value.cast(self.program.size_t, True)
			
			address = self.program.builder.gep(self.array, [index.opcode])
			self.program.builder.store(value.opcode, address)


if __debug__ and __name__ == '__main__':
	Test0 = Program('Test0')
	
	Test0.variable('a', c_int32)
	Test0['a'] = 1
	assert Test0['a'] == 1
	
	Test0.variable('b', c_int16 * 10)
	Test0['b'] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
	assert Test0['b'][2] == 3
	Test0['b'][5] = 0
	Test0['a'] = Test0['b'][1]
	assert Test0['a'] == Test0['b'][1]
	
	Test0.variable('bb', c_int8 * 3)
	Test0['bb'] = [9, 9, 9]
	Test0['a'] = 200
	Test0['bb'][0] = Test0['a']
	
	with Test0.function('c', [c_int16, c_int16], c_int32) as c:
		c.return_ = 7
	
	with Test0.function('d', [c_int16, c_int16], c_int16) as d:
		x, y = d.arguments
		d.variable('da', c_int16)
		d.variable('db', c_int16 * 2)
		d['da'] = x
		d['db'] = [y, d['da']]
		d['db'][0] += d['db'][1]
		d.return_ = d['da'] + d['db'][1]
	
	@Test0
	def e(i:c_int16, v:c_int16) -> c_int16:
		b = Test0['b']
		k: c_int16 = 1
		kk: c_int8 * 10
		
		k = b[0]
		kk[2] = 2
		b[i] = v + k
		return b[i + 1]
	
	with Test0.function('f', [c_int16], c_int32) as f:
		x, = f.arguments
		
		'''
		int32_t z = 0;
		for(int32_t y = 0; y < 10; y++)
			z += y;
		'''
		
		f.variable('z', c_int32)
		f['z'] = 0
		
		for y in f.for_loop(10):
			f['z'] += y
		
		f.return_ = f['z']
	
	with Test0.function('g', [c_int16, c_int16], c_int32) as g:
		x, y = g.arguments
		
		g.variable('n', c_int32)
		
		for a in g.for_loop(x):
			for b in g.for_loop(y):
				g['n'] += 1
		
		g.return_ = g['n']
	
	with Test0.function('h', [c_int32], c_int32) as h:
		x, = f.arguments
		
		h.variable('a', c_int32)
		
		h['a'] = 1
		
		test_block = current_block
		yes_block = append_block()
		no_block = append_block()
		landing_block = append_block()
		
		test_block.cbranch(x.nonzero(), yes_block, no_block)
		
		for t0 in [True, False]:
			if t0:
				current_block = yes_block
			else:
				current_block = no_block
			
			if t0:
				h['a'] += 2
				for t1 in [True, False]:
					if h['a'].nonzero() == t1:
						h['a'] += 7
			else:
				for t2 in [True, False]:
					if not x.nonzero() == t2:
						h['a'] += 5
		
		h.return_ = h['a']
	
	
	
	print(Test0.llvm_source())
	print()
	
	print(Test0.c_header())
	
	'''
	@Program
	class Test1:
		f: c_int8
		g: c_int8 * 16
		cc: Final[c_int16] = 9
		dd: Final[c_int16 * 2] = [3, 4]
		
		def a(self, x:c_int16, y:c_int8) -> c_int16:
			self.g[5] = 127 * self.f + 1
			return self.cc + self.dd[x]
		
		def b(self, x:c_int8) -> c_int16:
			y:c_int16 = 0
			for n in _function_symbol.for_loop(x):
				y += n
				self.f = y * 2
			return y
	
	print(Test1._program.llvm_source())
	'''

