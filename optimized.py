#!/usr/bin/python3


__all__ = 'initialize_llvm', 'optimize'


from enum import Enum
from ctypes import CFUNCTYPE, c_int, c_uint8, c_int16, POINTER
from llvmlite.ir import Module, IntType, ArrayType, Constant, GlobalVariable, FunctionType, Function, IRBuilder
from llvmlite.ir._utils import DuplicatedNameError
from llvmlite.binding import initialize, initialize_native_target, initialize_native_asmprinter, parse_assembly, create_mcjit_compiler, Target, get_process_triple
from collections import defaultdict
from collections.abc import Iterable

from tracing import *


bool_t = IntType(1)
byte_t = IntType(8)
short_t = IntType(16)
long_t = IntType(32)


def build_array(module, name, int_t, array):
	array_t = ArrayType(int_t, len(array._SymbolicValue__operands))
	result = GlobalVariable(module, array_t, name)
	result.initializer = array_t([int_t(_n._SymbolicValue__operands) for _n in array._SymbolicValue__operands])
	result.global_constant = True


def build_function(module, name, args_t, return_t, int_t, size_t, expr):
	"""
	module - llvmlite module
	name - function name
	args_t - list of function arg types
	return_t - function return type
	int_t - type for arithmetics, should be 2 times bigger than args and return
	size_t - type for list indices, should be bigger than the biggest array and number of loop iterations, plus 1 sign bit
	expr - SymbolicValue, function body
	
	int_t, size_t and expr may be None, in that case a declaration will be created
	"""
	
	function_t = FunctionType(return_t, args_t)
	try:
		function = Function(module, function_t, name)
	except DuplicatedNameError:
		function = module.get_global(name)
	assert function.type.pointee == function_t, f"{function.type} == {function_t}"
	
	if expr is None:
		assert function.is_declaration
		return
	
	def find_loop_in(expr):
		if not hasattr(expr, '_SymbolicValue__mnemonic'):
			return
		
		if expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_IN:
			yield expr
		
		try:
			oo = iter(expr._SymbolicValue__operands)
		except TypeError:
			pass
		else:
			for sexpr in oo:
				yield from find_loop_in(sexpr)
	
	def convert_args(args, ops, builder):
		if args[0].type != args[1].type:
			if args[0].type.width > args[1].type.width:
				if ops[1]._SymbolicValue__type == expr.Type.UINT:
					args[1] = builder.zext(args[1], args[0].type)
				elif ops[1]._SymbolicValue__type == expr.Type.INT:
					args[1] = builder.sext(args[1], args[0].type)
				else:
					raise RuntimeError
			
			elif args[0].type.width < args[1].type.width:
				if ops[0]._SymbolicValue__type == expr.Type.UINT:
					args[0] = builder.zext(args[0], args[1].type)
				elif ops[0]._SymbolicValue__type == expr.Type.INT:
					args[0] = builder.sext(args[0], args[1].type)
				else:
					raise RuntimeError
			
			else:
				raise RuntimeError
	
	def assemble(expr, builder):
		#print("assemble", builder.block.name, expr._SymbolicValue__mnemonic.name)
		if expr._SymbolicValue__mnemonic == expr.Mnemonic.CALL or (isinstance(expr._SymbolicValue__operands, Iterable) and not isinstance(expr._SymbolicValue__operands, str)):
			if expr._SymbolicValue__mnemonic == expr.Mnemonic.IF:
				c, yes, no = expr._SymbolicValue__operands
				
				if isinstance(c, SymbolicValue) and c._SymbolicValue__mnemonic != expr.Mnemonic.CONST:
					c, c_builder = assemble(c, builder)
					if c.type != bool_t:
						c = c_builder.icmp_signed('!=', c, c.type(0))
					
					yes_builder_enter = IRBuilder(function.append_basic_block())
					yes_builder_enter.comment("yes case")
					yes_r, yes_builder_exit = assemble(yes, yes_builder_enter)
					no_builder_enter = IRBuilder(function.append_basic_block())
					no_builder_enter.comment("no case")
					no_r, no_builder_exit = assemble(no, no_builder_enter)
					
					assert yes_r.type == no_r.type
					
					c_builder.comment("if?")
					c_builder.cbranch(c, yes_builder_enter.block, no_builder_enter.block)
					r_builder = IRBuilder(function.append_basic_block())
					yes_builder_exit.comment("join after conditional (from yes)")
					yes_builder_exit.branch(r_builder.block)
					no_builder_exit.comment("join after conditional (from no)")
					no_builder_exit.branch(r_builder.block)
					
					phi = r_builder.phi(yes_r.type)
					phi.add_incoming(yes_r, yes_builder_exit.block)
					phi.add_incoming(no_r, no_builder_exit.block)
					return phi, r_builder
				else:
					raise NotImplementedError
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_CNT:
				loop_id, iter_num = expr._SymbolicValue__operands
				
				if (loop_id, '__counter') in loop_var:
					var, _, _ = loop_var[loop_id, '__counter']
					return var, builder
				
				enter_builder = loop_enter[loop_id]
				enter_builder.comment(f"loop {loop_id} counter")
				var = enter_builder.phi(size_t)
				#var.add_incoming(size_t(0), old_builder.block)
				
				loop_var[loop_id, '__counter'] = var, 0, iter_num
				
				return var, builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_IN:
				loop_no, var_name, in_expr = expr._SymbolicValue__operands
				
				if loop_no not in loop_before: # LOOP_IN outside corresponding LOOP_OUT (invariant)
					return assemble(in_expr, builder) # return initial value unchanged
				
				assert loop_no in loop_before
				assert loop_no in loop_enter
				assert loop_no in loop_begin
				assert loop_no in loop_body
				assert loop_no in loop_exit
				assert loop_no in loop_after
				
				if (loop_no, var_name) in loop_var:
					var, in_result, out_result = loop_var[loop_no, var_name]
				else:
					var = in_result = out_result = None
				
				if in_result is None:
					before_builder = loop_before[loop_no]
					in_result, before_builder = assemble(in_expr, before_builder) # calculate initial value in the block before the loop
					loop_before[loop_no] = before_builder
					#print(f"created in var {var_name}")
				
				if var is None:
					if expr._SymbolicValue__length is not None: # array
						var = in_result
					else: # scalar
						enter_builder = loop_enter[loop_no]
						enter_builder.comment(f"loop {loop_no} variable {var_name}")
						var = enter_builder.phi(in_result.type)			
				
				loop_var[loop_no, var_name] = var, in_result, out_result
				
				#print(f"returned in var {var_name}", in_result, out_result)
				return var, builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_OUT:
				loop_no, var_name, out_expr = expr._SymbolicValue__operands
				
				arg_builder = builder
				del builder
				
				if loop_no in loop_before:
					before_builder = loop_before[loop_no]
					loop_first_time = False
				else:
					before_builder = loop_before[loop_no] = IRBuilder(function.append_basic_block())
					before_builder.comment(f"before loop {loop_no}")
					loop_first_time = True
				
				if loop_no in loop_enter:
					enter_builder = loop_enter[loop_no]
				else:
					enter_builder = loop_enter[loop_no] = IRBuilder(function.append_basic_block())
					enter_builder.comment(f"enter loop {loop_no}")
				
				if loop_no in loop_body:
					assert loop_no in loop_begin
					body_builder = loop_body[loop_no]
				else:
					body_builder = loop_body[loop_no] = loop_begin[loop_no] = IRBuilder(function.append_basic_block())
					body_builder.comment(f"begin loop {loop_no}")
				
				if loop_no in loop_exit:
					exit_builder = loop_exit[loop_no]
				else:
					exit_builder = loop_exit[loop_no] = IRBuilder(function.append_basic_block())
					exit_builder.comment(f"exit loop {loop_no}")
				
				if loop_no in loop_after:
					after_builder = loop_after[loop_no]
				else:
					after_builder = loop_after[loop_no] = IRBuilder(function.append_basic_block())
					after_builder.comment(f"after loop {loop_no}")
				
				if loop_first_time:
					arg_builder.comment(f"execute loop {loop_no}")
					arg_builder.branch(before_builder.block)
					
					ret_builder = after_builder
					ret_builder.comment(f"return from loop {loop_no}")
					#print("execute loop", loop_no, "from", arg_builder.block.name, "returning to", ret_builder.block.name)
				else:
					ret_builder = arg_builder
				
				if (loop_no, var_name) in loop_var:
					var, in_result, out_result = loop_var[loop_no, var_name]
				else:
					var = in_result = out_result = None
				
				if out_result is None:
					#print("{", loop_no, var_name, body_builder.block.name)
					out_result, body_builder = assemble(out_expr, body_builder) # calculate result of loop variable
					#print("}", loop_no, var_name, body_builder.block.name)
					loop_body[loop_no] = body_builder
					#print(f"created out var {var_name}")
				
				if (loop_no, var_name) in loop_var: # in var might have been created through out_expr
					var, in_result, _ = loop_var[loop_no, var_name]
				
				if var is None:
					enter_builder.comment(f"loop {loop_no} variable {var_name}")
					var = enter_builder.phi(out_result.type)
				
				loop_var[loop_no, var_name] = var, in_result, out_result
				
				#print(f" return from loop var {var_name}", loop_first_time, arg_builder.block.name, ret_builder.block.name)
				return var, ret_builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.CALL:
				fn = expr._SymbolicValue__operands[0]
				if isinstance(fn, SymbolicValue):
					fn, builder = assemble(fn, builder)
				
				def type_listcomp(expr, lltype):
					if not hasattr(expr, '_SymbolicValue__mnemonic'):
						return expr
					elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LISTCOMP:
						return expr.__class__(expr.Mnemonic.LISTCOMP, expr._SymbolicValue__type, expr._SymbolicValue__length, lltype)
					else:
						try:
							if isinstance(expr._SymbolicValue__operands, str):
								raise TypeError
							oo = iter(expr._SymbolicValue__operands)
						except TypeError:
							return SymbolicValue(mnemonic=expr._SymbolicValue__mnemonic, type_=expr._SymbolicValue__type, length=expr._SymbolicValue__length, operands=type_listcomp(expr._SymbolicValue__operands, lltype))
						else:
							return SymbolicValue(mnemonic=expr._SymbolicValue__mnemonic, type_=expr._SymbolicValue__type, length=expr._SymbolicValue__length, operands=[type_listcomp(_sexpr, lltype) for _sexpr in oo])
				
				args = []
				for e, tt in zip(expr._SymbolicValue__operands[1:], fn.type.pointee.args):
					if hasattr(tt, 'pointee') and e._SymbolicValue__mnemonic == expr.Mnemonic.LOOP_OUT and e._SymbolicValue__length is not None:
						e = type_listcomp(e, tt.pointee.element)
					
					if isinstance(e, SymbolicValue):
						r, builder = assemble(e, builder) # function argument
					else:
						r = e
					
					args.append(r)
				
				tr_args = []
				for a, tt in zip(args, fn.type.pointee.args):
					if isinstance(a, list):
						alloc_builder.comment("list arg")
						l = alloc_builder.alloca(tt.pointee)
						for n, el in enumerate(a):
							p = builder.gep(l, [size_t(0), size_t(n)])
							v = builder.trunc(el, tt.pointee.element)
							builder.store(v, p)
						a = l
					elif a.type != tt:
						a = builder.trunc(a, tt)
					tr_args.append(a)
				
				r = builder.call(fn, tr_args)
				if expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.INT:
					r = builder.sext(r, int_t)
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.UINT:
					r = builder.zext(r, int_t)
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
				
				return r, builder
			
			else:
				args = []
				for e in expr._SymbolicValue__operands:
					if isinstance(e, SymbolicValue):
						r, builder = assemble(e, builder) # generic value
					else:
						r = e
					
					assert not isinstance(r, list), str(e)
					
					args.append(r)
			
			if expr._SymbolicValue__mnemonic == expr.Mnemonic.CONST:
				if expr._SymbolicValue__type == expr.Type.LIST_INT or expr._SymbolicValue__type == expr.Type.LIST_UINT:
					assert len(expr._SymbolicValue__operands) == len(args)
					at = ArrayType(int_t, expr._SymbolicValue__length)
					alloc_builder.comment("const list")
					ar = alloc_builder.alloca(at)
					for n, v in enumerate(args):
						p = builder.gep(ar, [size_t(0), size_t(n)])
						if v.type == int_t:
							cv = v
						else:
							cv = builder.zext(v, int_t)
						builder.store(cv, p)
					return ar, builder
				else:
					raise NotImplementedError(str(expr._SymbolicValue__type))
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.INDEX:
				p = builder.gep(args[0], [size_t(0), args[1]])
				r = builder.load(p)
				
				if expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.LIST_UINT:
					q = builder.zext(r, int_t)
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type == expr.Type.LIST_INT:
					#builder.comment("signed int array element")
					q = builder.sext(r, int_t)
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
				
				return q, builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.XOR:
				convert_args(args, expr._SymbolicValue__operands, builder)
				return builder.xor(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.ADD:
				convert_args(args, expr._SymbolicValue__operands, builder)
				return builder.add(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.SUB:
				convert_args(args, expr._SymbolicValue__operands, builder)
				return builder.sub(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.MUL:
				convert_args(args, expr._SymbolicValue__operands, builder)
				return builder.mul(args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.POW:
				try:
					if args[0].constant != 2:
						raise NotImplementedError("Only power of 2 is supported.")
				except AttributeError:
					raise NotImplementedError("Only constant base powe is supported.")
				
				return builder.shl(args[0].type(1), builder.trunc(args[1], args[0].type)), builder # power is shift left
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.GE:
				return builder.icmp_signed('>=', args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.EQ:
				return builder.icmp_signed('==', args[0], args[1]), builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.FLOORDIV:
				if expr._SymbolicValue__operands[1]._SymbolicValue__type != expr.Type.UINT:
					raise NotImplementedError(str(expr._SymbolicValue__operands[1]._SymbolicValue__type))
				
				if expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.INT:
					convert_args(args, expr._SymbolicValue__operands, builder)
					return builder.udiv(args[0], args[1]), builder # udiv in Python semantics
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.UINT:
					convert_args(args, expr._SymbolicValue__operands, builder)
					return builder.udiv(args[0], args[1]), builder
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.MOD:
				if expr._SymbolicValue__operands[1]._SymbolicValue__type != expr.Type.UINT:
					raise NotImplementedError(str(expr._SymbolicValue__operands[1]._SymbolicValue__type))
				
				if expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.INT:
					convert_args(args, expr._SymbolicValue__operands, builder)
					p0 = builder.mul(args[1], args[1].type(255))
					p1 = builder.add(args[0], p0)
					return builder.urem(p1, args[1]), builder # urem in Python semantics
				elif expr._SymbolicValue__operands[0]._SymbolicValue__type != expr.Type.UINT:
					convert_args(args, expr._SymbolicValue__operands, builder)
					return builder.urem(args[0], args[1]), builder
				else:
					raise NotImplementedError(str(expr._SymbolicValue__operands[0]._SymbolicValue__type))
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.STORE:
				p = builder.gep(args[0], [size_t(0), args[1]])
				v = builder.trunc(args[2], args[0].type.pointee.element)
				builder.store(v, p)
				return args[0], builder
			
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.SLICE:
				#i = builder.mul(args[0], args[0].type(expr._SymbolicValue__length))
				p = builder.gep(args[1], [size_t(0), args[0]])
				v = builder.bitcast(p, ArrayType(args[1].type.pointee.element, expr._SymbolicValue__length).as_pointer())
				return v, builder
			
			else:
				raise NotImplementedError(str(expr))
		
		else:
			if expr._SymbolicValue__mnemonic == expr.Mnemonic.CONST:
				return int_t(expr._SymbolicValue__operands), builder
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.ARG:
				a = function.args[expr._SymbolicValue__operands]
				if expr._SymbolicValue__type == expr.Type.UINT:
					r = builder.zext(a, int_t)
				elif expr._SymbolicValue__type == expr.Type.INT:
					#builder.comment("signed int formal arg")
					r = builder.sext(a, int_t)
				elif expr._SymbolicValue__type == expr.Type.LIST_INT or expr._SymbolicValue__type == expr.Type.LIST_UINT:
					r = a
				else:
					raise NotImplementedError(str(expr._SymbolicValue__type))
				return r, builder
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.PTR:
				return module.get_global(expr._SymbolicValue__operands), builder
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.FUN:
				return module.get_global(expr._SymbolicValue__operands), builder
			elif expr._SymbolicValue__mnemonic == expr.Mnemonic.LISTCOMP:
				lltype = expr._SymbolicValue__operands
				#assert lltype is not None
				
				if lltype is None:
					lltype = byte_t #FIXME: deduce correct type from argument or return value
				assert isinstance(expr._SymbolicValue__length, int)
				alloc_builder.comment("listcomp")
				lc = alloc_builder.alloca(ArrayType(lltype, expr._SymbolicValue__length))
				for lcn in range(expr._SymbolicValue__length):
					p = builder.gep(lc, [size_t(0), size_t(lcn)])
					builder.store(lltype(0), p)
				return lc, builder
			
			else:
				raise NotImplementedError(str(expr))
	
	loop_var = {} # loop variables
	loop_before = {} # block before the loop, calculate initial values
	loop_enter = {} # loop head, merge initial and update values, increment counter, jump to begin or exit block
	loop_begin = {} # loop start, first block in loop body
	loop_body = {} # current (last) block in loop body
	loop_exit = {} # loop exit block; TODO: implement exceptions
	loop_after = {} # block after the loop
	
	alloc_builder = IRBuilder(function.append_basic_block()) # block with table allocations
	
	begin_builder = builder = IRBuilder(function.append_basic_block()) # first code block in the function
	builder.comment(f"begin function {name}")
	result, builder = assemble(expr, builder) # build function result
	if isinstance(result, list):
		assert return_t == args_t[-1]
		assert len(result) == return_t.pointee.count, f"{function_t} ;;; {function.type}"
		r = function.args[len(args_t) - 1]
		for n, val in enumerate(result):
			p = builder.gep(r, [size_t(0), size_t(n)])
			v = builder.trunc(val, return_t.pointee.element)
			builder.store(v, p)
	elif hasattr(return_t, 'pointee') and hasattr(return_t.pointee, 'element'):
		assert return_t == args_t[-1]
		assert result.type == return_t
		r = function.args[len(args_t) - 1]
		for n in range(return_t.pointee.count):
			pr = builder.gep(r, [size_t(0), size_t(n)])
			pv = builder.gep(result, [size_t(0), size_t(n)])
			v = builder.load(pv)
			builder.store(v, pr)
	else:
		r = builder.trunc(result, return_t)
	
	builder.ret(r)
	builder.comment(f"end function {name}")
	
	alloc_builder.branch(begin_builder.block)

	for loop_no, builder in loop_before.items():
		builder.branch(loop_enter[loop_no].block)
	
	for loop_no, builder in loop_body.items():
		var, _, _ = loop_var[loop_no, '__counter']
		var_plus_1 = builder.add(var, size_t(1))
		builder.branch(loop_enter[loop_no].block)
		builder.comment(f"end loop {loop_no}")
		var.add_incoming(size_t(0), loop_before[loop_no].block)
		var.add_incoming(var_plus_1, builder.block)
	
	for loop_no, builder in loop_enter.items():
		var, _, iter_num = loop_var[loop_no, '__counter']
		builder.comment(f"loop {loop_no} iteration limit {iter_num}")
		iter_num = size_t(iter_num)
		c = builder.icmp_signed('<', var, iter_num)
		builder.cbranch(c, loop_begin[loop_no].block, loop_exit[loop_no].block)
	
	for loop_no, builder in loop_exit.items():
		builder.branch(loop_after[loop_no].block)
	
	for (loop_no, var_name), (var, in_result, out_result) in loop_var.items():
		if var_name == '__counter': continue
		if hasattr(var, 'add_incoming'):
			#print(var_name, in_result, out_result)
			var.add_incoming(in_result, loop_before[loop_no].block)
			var.add_incoming(out_result, loop_body[loop_no].block)


def optimize(Field, Linear, Quadratic, LinearCircuit, QuadraticCircuit, linearcircuit_call_types=[], quadraticcircuit_call_types=[], debug=False):
	module = Module()
	
	OptimizedField = type(Field.__name__, (Field,), {})
	OptimizedLinear = type('Linear', (Linear,), {})
	OptimizedQuadratic = type('Quadratic', (Quadratic,), {})
	OptimizedLinearCircuit = type('LinearCircuit', (LinearCircuit,), {})
	OptimizedQuadraticCircuit = type('QuadraticCircuit', (QuadraticCircuit,), {})
	
	exp_table = OptimizedField.exponent
	log_table = OptimizedField.logarithm
	build_array(module, 'Field.exponent', byte_t, SymbolicValue(OptimizedField.exponent))
	build_array(module, 'Field.logarithm', byte_t, SymbolicValue(OptimizedField.logarithm))
	
	OptimizedField.exponent = SymbolicValue._ptr_list_uint('Field.exponent', 256)
	OptimizedField.logarithm = SymbolicValue._ptr_list_uint('Field.logarithm', 256)
	
	if debug: trees = open('trees.txt', 'w')
	
	field_sum_types = set()
	orig_field_sum = OptimizedField.sum
	py_field_sum = transform(OptimizedField.sum, 'BinaryGalois')
	#py_field_sum = Field.sum
	def field_sum_capture(l):
		if not isinstance(l, SymbolicValue):
			l = symbolize(l)[1]
		
		if not isinstance(l, SymbolicValue):
			tl = [symbolize(_a) for _a in l]
			t, l = zip(*tl)
		
		if len(l) not in field_sum_types:
			field_sum_types.add(len(l))
			build_function(module, f'Field.sum_{len(l)}', [ArrayType(byte_t, len(l)).as_pointer()], byte_t, None, None, None)
		return SymbolicValue._fun_uint(f'Field.sum_{len(l)}')(l)
	#Field.sum = field_sum_capture
	OptimizedField.sum = lambda _l: OptimizedField(py_field_sum(SymbolicArray(symbolize(_l)[1], [None], [OptimizedField])))
	
	if debug: print("optimizing multiplication")
	body = optimize_expr(symbolize(trace(transform(OptimizedField.__mul__, 'BinaryGalois'), [OptimizedField(SymbolicValue._arg_uint(0)), OptimizedField(SymbolicValue._arg_uint(1))]))[1])
	if debug: print('Field.__mul__', file=trees)
	if debug: body._print_tree(file=trees)
	if debug: print(file=trees)
	build_function(module, 'Field.__mul__', [byte_t, byte_t], byte_t, short_t, long_t, body)
	OptimizedField.__mul__ = lambda _a, _b: OptimizedField(SymbolicValue._fun_uint('Field.__mul__')(symbolize(_a)[1], symbolize(_b)[1]))
	
	if debug: print("optimizing exponentiation")
	body = optimize_expr(symbolize(trace(transform(OptimizedField.__pow__, 'BinaryGalois'), [OptimizedField(SymbolicValue._arg_uint(0)), SymbolicValue._arg_int(1)]))[1])
	if debug: print('Field.__pow__', file=trees)
	if debug: body._print_tree(file=trees)
	if debug: print(file=trees)
	build_function(module, 'Field.__pow__', [byte_t, short_t], byte_t, short_t, long_t, body)
	OptimizedField.__pow__ = lambda _a, _b: OptimizedField(SymbolicValue._fun_uint('Field.__pow__')(symbolize(_a)[1], symbolize(_b)[1]))
	
	if debug: print("optimizing linear")
	py_linear_call = transform(OptimizedLinear.__call__, 'Linear')
	body = optimize_expr(symbolize(trace(py_linear_call, [OptimizedLinear(SymbolicArray(SymbolicValue._arg_list_uint(0, OptimizedField.field_power), [None], [OptimizedField])), OptimizedField(SymbolicValue._arg_uint(1))]))[1])
	if debug: print('Linear.__call__', file=trees)
	if debug: body._print_tree(file=trees)
	if debug: print(file=trees)
	build_function(module, 'Linear.__call__', [ArrayType(byte_t, OptimizedField.field_power).as_pointer(), byte_t], byte_t, short_t, long_t, body)
	OptimizedLinear.__call__ = lambda _l, _f: OptimizedField(py_linear_call(_l, OptimizedField(symbolize(_f)[1])))
	
	if debug: print("optimizing quadratic")
	body = optimize_expr(symbolize(trace(transform(OptimizedQuadratic.__call__, 'Quadratic'), [OptimizedQuadratic(SymbolicArray(SymbolicValue._arg_list_uint(0, OptimizedField.field_power**2), [OptimizedField.field_power, None], [OptimizedLinear, OptimizedField])), OptimizedField(SymbolicValue._arg_uint(1)), OptimizedField(SymbolicValue._arg_uint(2))]))[1])
	if debug: print('Quadratic.__call__', file=trees)
	if debug: body._print_tree(file=trees)
	if debug: print(file=trees)
	build_function(module, 'Quadratic.__call__', [ArrayType(byte_t, OptimizedField.field_power**2).as_pointer(), byte_t, byte_t], byte_t, short_t, long_t, body)
	OptimizedQuadratic.__call__ = lambda _q, _f1, _f2: OptimizedField(SymbolicValue._fun_uint('Quadratic.__call__')(symbolize(_q)[1], symbolize(_f1)[1], symbolize(_f2)[1]))
	
	if debug: print("optimizing linear circuit")
	linearcircuit_call_types = set()
	orig_linearcircuit_call = OptimizedLinearCircuit.__call__
	py_linearcircuit_call = OptimizedLinearCircuit.__call__
	def linearcircuit_call_capture(lc, iv):
		if not isinstance(lc, SymbolicValue):
			lc = symbolize(lc)[1]
		
		if not isinstance(iv, SymbolicValue):
			iv = symbolize(iv)[1]
		
		len_lc = len(lc) // OptimizedField.field_power
		len_iv = len(iv)
		assert len_lc % len_iv == 0, f"{len_lc}, {len_iv}"
		len_ov = len_lc // len_iv
		
		if (len_ov, len_iv) not in linearcircuit_call_types:
			linearcircuit_call_types.add((len_ov, len_iv))
			#build_function(module, f'LinearCircuit.__call__{len_ov}_{len_iv}', [ArrayType(byte_t, len_lc * OptimizedField.field_power).as_pointer(), ArrayType(byte_t, len_iv).as_pointer(), ArrayType(byte_t, len_ov).as_pointer()], ArrayType(byte_t, len_ov).as_pointer(), None, None, None)
		return SymbolicValue._fun_uint(f'LinearCircuit.__call__{len_ov}_{len_iv}')(lc, iv)
	OptimizedLinearCircuit.__call__ = linearcircuit_call_capture
	
	for output_size, input_size in linearcircuit_call_types:
		lc = OptimizedLinearCircuit(SymbolicTable(SymbolicValue._arg_list_uint(0, OptimizedField.field_power * output_size * input_size), [output_size, input_size], [OptimizedField.field_power, None], [OptimizedLinear, OptimizedField]))
		iv = Vector(SymbolicArray(SymbolicValue._arg_list_uint(1, input_size), [None], [OptimizedField]))
		tr = lc(iv)
	
	#print("optimizing quadratic circuit")
	quadraticcircuit_call_types = set()
	orig_quadraticcircuit_call = OptimizedQuadraticCircuit.__call__
	py_quadraticcircuit_call = OptimizedQuadraticCircuit.__call__
	def quadraticcircuit_call_capture(qc, iv):
		if not isinstance(qc, SymbolicValue):
			qc = symbolize(qc)[1]
		
		if not isinstance(iv, SymbolicValue):
			iv = symbolize(iv)[1]
		
		assert isinstance(qc, SymbolicValue), type(qc).__name__
		
		len_qc = len(qc) // OptimizedField.field_power**2
		len_iv = len(iv)
		assert len_qc % len_iv**2 == 0, f"{len_qc}, {len_iv}"
		len_ov = len_qc // len_iv**2
		
		assert len(qc) == len(iv)**2 * len_ov * OptimizedField.field_power**2
		
		if (len_ov, len_iv) not in quadraticcircuit_call_types:
			quadraticcircuit_call_types.add((len_ov, len_iv))
			#build_function(module, f'QuadraticCircuit.__call__{len_ov}_{len_iv}', [ArrayType(byte_t, len_lc * OptimizedField.field_power).as_pointer(), ArrayType(byte_t, len_iv).as_pointer(), ArrayType(byte_t, len_ov).as_pointer()], ArrayType(byte_t, len_ov).as_pointer(), None, None, None)
		return SymbolicValue._fun_uint(f'QuadraticCircuit.__call__{len_ov}_{len_iv}')(qc, iv)
	OptimizedQuadraticCircuit.__call__ = quadraticcircuit_call_capture
	
	for output_size, input_size in quadraticcircuit_call_types:
		qc = OptimizedQuadraticCircuit(SymbolicTable(SymbolicValue._arg_list_uint(0, OptimizedField.field_power**2 * output_size * input_size**2), [output_size, input_size, input_size], [OptimizedField.field_power, OptimizedField.field_power, None], [OptimizedQuadratic, OptimizedLinear, OptimizedField]))
		iv = Vector(SymbolicArray(SymbolicValue._arg_list_uint(1, input_size), [None], [OptimizedField]))
		tr = qc(iv)
	
	#OptimizedField_sum_types.add(20)
	#OptimizedField_sum_types.add(12)
	#field_sum_types.add(144)
	#field_sum_types.add(289)
	#print("types:", field_sum_types, linearcircuit_call_types)
	
	'''
	for l in field_sum_types:
		body = symbolize(trace(py_field_sum, [SymbolicArray(SymbolicValue._arg_list_uint(0, l), [None], [OptimizedField])]))[1]
		build_function(module, f'Field.sum_{l}', [ArrayType(byte_t, l).as_pointer()], byte_t, short_t, long_t, body)
	'''
	
	for output_size, input_size in linearcircuit_call_types:
		lc = OptimizedLinearCircuit(SymbolicTable(SymbolicValue._arg_list_uint(0, OptimizedField.field_power * output_size * input_size), [output_size, input_size], [OptimizedField.field_power, None], [OptimizedLinear, OptimizedField]))
		assert lc.output_size == output_size
		assert lc.input_size == input_size
		iv = Vector(SymbolicArray(SymbolicValue._arg_list_uint(1, input_size), [None], [OptimizedField]))
		body = optimize_expr(symbolize(trace(transform(py_linearcircuit_call, 'LinearCircuit'), [lc, iv]))[1])
		if debug: print(f'LinearCircuit.__call__{output_size}_{input_size}', file=trees)
		if debug: body._print_tree(file=trees)
		if debug: print(file=trees)
		build_function(module, f'LinearCircuit.__call__{output_size}_{input_size}', [ArrayType(byte_t, input_size * output_size * OptimizedField.field_power).as_pointer(), ArrayType(byte_t, input_size).as_pointer(), ArrayType(byte_t, output_size).as_pointer()], ArrayType(byte_t, output_size).as_pointer(), short_t, long_t, body)
	
	for output_size, input_size in quadraticcircuit_call_types:
		qc = OptimizedQuadraticCircuit(SymbolicTable(SymbolicValue._arg_list_uint(0, OptimizedField.field_power**2 * output_size * input_size**2), [output_size, input_size, input_size], [OptimizedField.field_power, OptimizedField.field_power, None], [OptimizedQuadratic, OptimizedLinear, OptimizedField]))
		assert qc.output_size == output_size
		assert qc.input_size == input_size
		iv = Vector(SymbolicArray(SymbolicValue._arg_list_uint(1, input_size), [None], [OptimizedField]))
		body = optimize_expr(symbolize(trace(transform(py_quadraticcircuit_call, 'QuadraticCircuit'), [qc, iv]))[1])
		if debug: print(f'QuadraticCircuit.__call__{output_size}_{input_size}', file=trees)
		if debug: body._print_tree(file=trees)
		if debug: print(file=trees)
		build_function(module, f'QuadraticCircuit.__call__{output_size}_{input_size}', [ArrayType(byte_t, input_size**2 * output_size * OptimizedField.field_power**2).as_pointer(), ArrayType(byte_t, input_size).as_pointer(), ArrayType(byte_t, output_size).as_pointer()], ArrayType(byte_t, output_size).as_pointer(), short_t, long_t, body)
	
	if debug: trees.close()
	
	if debug:
		with open('module.ll', 'w') as f:
			print(module, file=f)
	
	if debug: print("compiling...")
	engine = create_mcjit_compiler(parse_assembly(str(module)), Target.from_triple(get_process_triple()).create_target_machine())
	engine.finalize_object()
	engine.run_static_constructors()
	if debug: print(" ready")
	
	'''
	def field_sum_bridge(l):
		if hasattr(l, 'serialize'):
			l = l.serialize()
			array_t = c_uint8 * len(l)
			l = array_t.from_buffer(l)
		else:
			l = [int(_v) for _v in l]
			array_t = c_uint8 * len(l)
			l = array_t(*l)
		
		c_field_sum = engine.get_function_address(f'Field.sum_{len(l)}')
		if not c_field_sum:
			raise NotImplementedError(f'Field.sum_{len(l)}')
		
		field_sum = CFUNCTYPE(c_uint8, array_t)(c_field_sum)
		return Field(field_sum(l))
	#Field.sum = field_sum_bridge
	'''
	OptimizedField.sum = orig_field_sum
	
	field_mul = CFUNCTYPE(c_uint8, c_uint8, c_uint8)(engine.get_function_address('Field.__mul__'))
	OptimizedField.__mul__ = lambda x, y: OptimizedField(field_mul(c_uint8(int(x)), c_uint8(int(y))))
	
	field_pow = CFUNCTYPE(c_uint8, c_uint8, c_int16)(engine.get_function_address('Field.__pow__'))
	OptimizedField.__pow__ = lambda x, y: OptimizedField(field_pow(c_uint8(int(x)), c_int16(y)))
	
	linear_array_t = c_uint8 * OptimizedField.field_power
	linear_call = CFUNCTYPE(c_uint8, linear_array_t, c_uint8)(engine.get_function_address('Linear.__call__'))
	OptimizedLinear.__call__ = lambda x, y: OptimizedField(linear_call(linear_array_t.from_buffer(x.serialize()), c_uint8(int(y))))
	
	quadratic_array_t = c_uint8 * OptimizedField.field_power**2
	quadratic_call = CFUNCTYPE(c_uint8, quadratic_array_t, c_uint8, c_uint8)(engine.get_function_address('Quadratic.__call__'))
	OptimizedQuadratic.__call__ = lambda x, y, z: OptimizedField(quadratic_call(quadratic_array_t.from_buffer(x.serialize()), c_uint8(int(y)), c_uint8(int(z))))
	
	def linearcircuit_call_bridge(lc, iv):
		assert lc.input_size == len(iv), f"{lc.input_size} == {len(iv)}"
		
		c_linearcircuit_call = engine.get_function_address(f'LinearCircuit.__call__{lc.output_size}_{lc.input_size}')
		if not c_linearcircuit_call:
			raise NotImplementedError(f'LinearCircuit.__call__{lc.output_size}_{lc.input_size}')
		
		assert len(list(lc.serialize())) == lc.output_size * lc.input_size * OptimizedField.field_power, f"{len(list(lc.serialize()))} == {lc.output_size * lc.input_size * OptimizedField.field_power}"
		
		lc_array_t = c_uint8 * (lc.output_size * lc.input_size * OptimizedField.field_power)
		iv_array_t = c_uint8 * lc.input_size
		ov_array_t = c_uint8 * lc.output_size
		
		linearcircuit_call = CFUNCTYPE(ov_array_t, lc_array_t, iv_array_t, ov_array_t)(c_linearcircuit_call)
		
		ov = Vector.zero(lc.output_size, lc.Array, lc.Field)
		linearcircuit_call(lc_array_t.from_buffer(lc.serialize()), iv_array_t.from_buffer(iv.serialize()), ov_array_t.from_buffer(ov.serialize()))
		return ov
	OptimizedLinearCircuit.__call__ = linearcircuit_call_bridge
	
	def quadraticcircuit_call_bridge(qc, iv):
		assert qc.input_size == len(iv)
		
		c_quadraticcircuit_call = engine.get_function_address(f'QuadraticCircuit.__call__{qc.output_size}_{qc.input_size}')
		if not c_quadraticcircuit_call:
			raise NotImplementedError(f'QuadraticCircuit.__call__{qc.output_size}_{qc.input_size}')
		
		assert len(list(qc.serialize())) == qc.output_size * qc.input_size**2 * OptimizedField.field_power**2, f"{len(list(qc.serialize()))} == {qc.output_size * qc.input_size**2 * OptimizedField.field_power**2}"
		
		qc_array_t = c_uint8 * (qc.output_size * qc.input_size**2 * OptimizedField.field_power**2)
		iv_array_t = c_uint8 * qc.input_size
		ov_array_t = c_uint8 * qc.output_size
		
		quadraticcircuit_call = CFUNCTYPE(ov_array_t, qc_array_t, iv_array_t, ov_array_t)(c_quadraticcircuit_call)
		
		ov = Vector.zero(qc.output_size, qc.Array, qc.Field)
		quadraticcircuit_call(qc_array_t.from_buffer(qc.serialize()), iv_array_t.from_buffer(iv.serialize()), ov_array_t.from_buffer(ov.serialize()))
		return ov
	OptimizedQuadraticCircuit.__call__ = quadraticcircuit_call_bridge

	OptimizedField.exponent = exp_table
	OptimizedField.logarithm = log_table
	
	# Keep references to compiled code.
	OptimizedField.__module = OptimizedLinear.__module = OptimizedQuadratic.__module = OptimizedLinearCircuit.__module = OptimizedQuadraticCircuit.__module = module
	OptimizedField.__engine = OptimizedLinear.__engine = OptimizedQuadratic.__engine = OptimizedLinearCircuit.__engine = OptimizedQuadraticCircuit.__engine = engine
	
	return OptimizedField, OptimizedLinear, OptimizedQuadratic, OptimizedLinearCircuit, OptimizedQuadraticCircuit


def initialize_llvm():
	initialize()
	initialize_native_target()
	initialize_native_asmprinter()


if __name__ == '__main__':
	from random import randrange
	
	from fields import Galois
	from linear import Linear, Quadratic, Vector
	from machines import Automaton, LinearCircuit, QuadraticCircuit
	from memory import Array, Table
	
	from pycallgraph2 import PyCallGraph
	from pycallgraph2.output.graphviz import GraphvizOutput
		
	initialize_llvm()
	
	Field = Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])
	
	test_vec_1 = [Field.random(randrange) for _n in range(Field.field_power)]
	test_vec_2 = [Field.random(randrange), Field.random(randrange)]
	test_vec_3 = [Field.random(randrange), randrange(Field.field_size)]
	test_vec_4 = [Linear.random(Array, Field, randrange), Field.random(randrange)]
	test_vec_5 = [Quadratic.random(Array, Linear, Field, randrange), Field.random(randrange), Field.random(randrange)]
	
	test_a = (Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]), test_vec_5[0](test_vec_5[1], test_vec_5[2]))
	#print(Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]))
	
	FieldO, LinearO, QuadraticO, LinearCircuitO, QuadraticCircuitO = optimize(Field, Linear, Quadratic, LinearCircuit, QuadraticCircuit, linearcircuit_call_types=[(4, 12), (8, 12), (8, 20), (12, 20)], quadraticcircuit_call_types=[(8, 12), (4, 12), (1, 17), (16, 17)], debug=True)
	
	test_b = (Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]), test_vec_5[0](test_vec_5[1], test_vec_5[2]))
	
	print(test_a)
	print(test_b)
	assert test_a == test_b
	#print(Field.sum(test_vec_1), test_vec_2[0] * test_vec_2[1], test_vec_3[0] ** test_vec_3[1], test_vec_4[0](test_vec_4[1]))
	
	#input_size = output_size = 8
	#lc = LinearCircuit({(_m, _n):Linear([Field(SymbolicValue._arg_list_uint(0, output_size * input_size * Field.field_power)[Field.field_power * input_size * _m + Field.field_power * _n + _k]) for _k in range(Field.field_power)]) for (_m, _n) in product(range(output_size), range(input_size))}, output_size=output_size, input_size=input_size)
	#v = Vector([Field(_v) for _v in SymbolicValue._arg_list_uint(1, Field.field_power)])
	#build_function(module, 'LinearCircuit.__call__', [..., ...], ..., trace(LinearCircuit.__call__, [lc, v]))
	
	def random_stream(length, size, Array, Field, randbelow):
		for n in range(length):
			yield Vector.random(size, Array, Field, randbelow)
	
	m_impl = 'llvm'
	
	print()
	a_str = list(random_stream(10, 8, Array, Field, randrange))	
	au = Automaton.random_linear_linear(8, 8, 12, Table, Array, Vector, LinearCircuit, Linear, Field, randrange)
	ao = Automaton.deserialize_linear_linear(8, 8, 12, Table, Array, Vector, LinearCircuitO, LinearO, FieldO, au.serialize())
	#with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_linear_linear_{Field.__name__}.png')):
	su = au.init_state[:]
	so = ao.init_state[:]
	print(su, so)
	assert su == so
	for n, (xu, xo) in enumerate(zip(au(a_str, su), ao(a_str, so), strict=True)):
		print(n, xu, xo)
		assert xu == xo
	print(su, so)
	assert su == so
	
	print()
	b_str = list(random_stream(10, 4, Array, Field, randrange))	
	bu = Automaton.random_linear_quadratic(4, 4, 8, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randrange)
	bo = Automaton.deserialize_linear_quadratic(4, 4, 8, Table, Array, Vector, QuadraticCircuitO, LinearCircuitO, QuadraticO, LinearO, FieldO, bu.serialize())
	#with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_linear_quadratic_{Field.__name__}.png')):
	su = bu.init_state[:]
	so = bo.init_state[:]
	print(su, so)
	assert su == so
	for n, (xu, xo) in enumerate(zip(bu(b_str, su), bo(b_str, so), strict=True)):
		print(n, xu, xo)
		assert xu == xo
	print(su, so)
	assert su == so
	
	print()
	c_str = list(random_stream(10, 4, Array, Field, randrange))	
	cu = Automaton.random_quadratic_linear(4, 4, 8, Table, Array, Vector, QuadraticCircuit, LinearCircuit, Quadratic, Linear, Field, randrange)
	co = Automaton.deserialize_quadratic_linear(4, 4, 8, Table, Array, Vector, QuadraticCircuitO, LinearCircuitO, QuadraticO, LinearO, FieldO, cu.serialize())
	#with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_quadratic_linear_{Field.__name__}.png')):
	su = cu.init_state[:]
	so = co.init_state[:]
	print(su, so)
	assert su == so
	for n, (xu, xo) in enumerate(zip(cu(c_str, su), co(c_str, so), strict=True)):
		print(n, xu, xo)
		assert xu == xo
	print(su, so)
	assert su == so
	
	print()
	d_str = list(random_stream(10, 1, Array, Field, randrange))
	du = Automaton.random_quadratic_quadratic(1, 1, 16, Table, Array, Vector, QuadraticCircuit, Quadratic, Linear, Field, randrange)
	do = Automaton.deserialize_quadratic_quadratic(1, 1, 16, Table, Array, Vector, QuadraticCircuitO, QuadraticO, LinearO, FieldO, du.serialize())
	#with PyCallGraph(output=GraphvizOutput(output_file=f'{m_impl}_quadratic_quadratic_{Field.__name__}.png')):
	su = du.init_state[:]
	so = do.init_state[:]
	print(su, so)
	assert su == so
	for n, (xu, xo) in enumerate(zip(du(d_str, su), do(d_str, so), strict=True)):
		print(n, xu, xo)
		assert xu == xo
	print(su, so)
	assert su == so


