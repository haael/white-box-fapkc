#!/usr/bin/python3


from enum import Enum, auto
from typing import Any, List, Tuple, Dict, Set
from typing import Self
from collections import defaultdict


class ExpressionError(Exception):
	"Base class for all expression-related exceptions."
	pass


class NotConvolvedFormError(ExpressionError):
	"Raised when an expression is not in the expected convolved form."
	pass


class NotDeconvolvedFormError(ExpressionError):
	"Raised when an expression is not in the expected deconvolved form."
	pass


class NotFlattenableError(ExpressionError):
	"Raised when an expression is not flattenable (not an ADD)."
	pass


class NotZeroRemovableError(ExpressionError):
	"Raised when an expression is not subject to zero removal (not an ADD or has no ZEROs)."
	pass


class NotOneRemovableError(ExpressionError):
	"Raised when an expression is not subject to one removal (not a MULTIPLY or has no UNITs)."
	pass


class ExpressionType(Enum):
	ZERO = auto()   # Represents "0" in addition
	UNIT = auto()  # Represents "1" in multiplication
	CONSTANT = auto()
	VARIABLE = auto()
	MULTIPLY = auto()
	ADD = auto()


class Expression:
	def __init__(self, type_: ExpressionType, operands: List[Any]):
		self.type_ = type_
		self.operands = operands

		# Validate and sort operands based on type_
		if self.type_ == ExpressionType.ADD:
			if len(self.operands) < 1:
				raise TypeError("ADD must have at least one operand")
			self.operands = sorted(self.operands)
		elif self.type_ == ExpressionType.MULTIPLY:
			if len(self.operands) != 2:
				raise TypeError("MULTIPLY must have exactly two operands")
			self.operands = sorted(self.operands)
		elif self.type_ == ExpressionType.VARIABLE:
			if len(self.operands) != 1 or not (isinstance(self.operands[0], int) or isinstance(self.operands[0], str)):
				raise ValueError("VARIABLE must have exactly one integer operand (variable index)")
		elif self.type_ == ExpressionType.CONSTANT:
			if len(self.operands) != 1:
				raise TypeError("CONSTANT must have exactly one operand")
		elif self.type_ == ExpressionType.UNIT:
			if len(self.operands) != 0:
				raise TypeError("UNIT must have no operands")
		elif self.type_ == ExpressionType.ZERO:
			if len(self.operands) != 0:
				raise TypeError("ZERO must have no operands")
		else:
			raise ValueError(f"Unknown expression type: {self.type_}")

	def __eq__(self, other: Any) -> bool:
		if not isinstance(other, Expression):
			return False
		return self.type_ == other.type_ and self.operands == other.operands

	def __hash__(self) -> int:
		return hash((self.type_, tuple(self.operands)))

	def __lt__(self, other: Self) -> bool:
		if not isinstance(other, Expression):
			raise TypeError("Cannot compare Expression with non-Expression")
		if self.type_ != other.type_:
			return self.type_.value < other.type_.value
		
		if self.type_ == ExpressionType.VARIABLE:
			if isinstance(self.operands[0], str) and isinstance(other.operands[0], int):
				return False
			elif isinstance(self.operands[0], int) and isinstance(other.operands[0], str):
				return True
			else:
				return self.operands[0] < other.operands[0]
		
		return self.operands < other.operands

	def __le__(self, other: Self) -> bool:
		return self == other or self < other

	def __gt__(self, other: Self) -> bool:
		return not (self <= other)

	def __ge__(self, other: Self) -> bool:
		return not (self < other)

	def __str__(self) -> str:
		if self.type_ == ExpressionType.ADD:
			return " + ".join(str(op) for op in self.operands)
		elif self.type_ == ExpressionType.MULTIPLY:
			left, right = self.operands
			if left.type_ not in {ExpressionType.ADD, ExpressionType.MULTIPLY} and right.type_ not in {ExpressionType.ADD, ExpressionType.MULTIPLY}:
				return f"{left}·{right}"
			else:
				return f"({left}) × ({right})"
		elif self.type_ == ExpressionType.VARIABLE:
			return f"input[{self.operands[0]}]"
		elif self.type_ == ExpressionType.CONSTANT:
			return str(self.operands[0])
		elif self.type_ == ExpressionType.UNIT:
			return "1"
		elif self.type_ == ExpressionType.ZERO:
			return "0"
		else:
			raise ValueError(f"Unknown expression type: {self.type_}")

	def __repr__(self) -> str:
		return f"Expression({self.type_}, {self.operands})"

	def flatten(self) -> Self:
		"Flattens nested additions. Raises NotFlattenableError if not an ADD."
		if self.type_ != ExpressionType.ADD:
			raise NotFlattenableError("Expression is not an ADD")

		new_operands = []
		for op in self.operands:
			if op.type_ == ExpressionType.ADD:
				new_operands.extend(op.operands)
			else:
				new_operands.append(op)

		return Expression(ExpressionType.ADD, new_operands)

	def remove_zero(self) -> Self:
		"Removes ZERO from operand list of addition. Returns ZERO if the list becomes empty."
		if self.type_ != ExpressionType.ADD:
			raise NotZeroRemovableError("Expression is not an ADD")

		new_operands = [op for op in self.operands if op.type_ != ExpressionType.ZERO]

		if not new_operands:
			return Expression(ExpressionType.ZERO, [])
		else:
			return Expression(ExpressionType.ADD, new_operands)

	def remove_one(self) -> Self:
		"Removes UNIT from multiplication. Returns the other operand."
		if self.type_ != ExpressionType.MULTIPLY:
			raise NotOneRemovableError("Expression is not a MULTIPLY")

		left, right = self.operands
		if left.type_ == ExpressionType.UNIT:
			return right
		elif right.type_ == ExpressionType.UNIT:
			return left
		else:
			raise NotOneRemovableError("Expression has no UNIT operand")

	def zero_product(self) -> Self:
		"Returns ZERO if the expression is a multiplication by ZERO."
		if self.type_ != ExpressionType.MULTIPLY:
			raise NotDeconvolvedFormError("Expression is not a MULTIPLY")

		left, right = self.operands
		if left.type_ == ExpressionType.ZERO or right.type_ == ExpressionType.ZERO:
			return Expression(ExpressionType.ZERO, [])
		return self
	
	def deconvolve(self) -> Self:
		"Applies distributivity: a0*b0 + a0*b1 + ... -> (a0 + ...) * (b0 + ...)"
		if self.type_ != ExpressionType.ADD:
			raise NotConvolvedFormError("Expression is not an ADD")
		
		factors = defaultdict(set)
		
		for term in self.operands:
			if term.type_ == ExpressionType.MULTIPLY:
				left, right = term.operands
			else:
				left = term
				right = Expression(ExpressionType.UNIT, [])
				#raise NotConvolvedFormError("All terms must be MULTIPLY")
			#left_factors.add(left)
			#right_factors.add(right)
			
			factors[left].add(right)
			factors[right].add(left)
		
		addends = defaultdict(set)
		for k, v in factors.items():
			addends[frozenset(v)].add(k)
		
		#for k, v in addends.items():
		#	print([str(_e) for _e in k], [str(_e) for _e in v])
		
		if len(addends) != 2 or frozenset({Expression(ExpressionType.UNIT, [])}) in addends:
			raise NotConvolvedFormError
		
		a, b = list(addends.keys())
		
		result = Expression(ExpressionType.MULTIPLY, [Expression(ExpressionType.ADD, a), Expression(ExpressionType.ADD, b)])
		return result
		
		# If all terms share a common left or right factor, it's not a convolution
		#if len(left_factors) == 1 or len(right_factors) == 1:
		#	raise NotConvolvedFormError("Not a convolution (common factor)")

		# Build the deconvolved expression: (sum(left_factors)) * (sum(right_factors))
		#sum_left = Expression(ExpressionType.ADD, list(left_factors))
		#sum_right = Expression(ExpressionType.ADD, list(right_factors))
		#return Expression(ExpressionType.MULTIPLY, [sum_left, sum_right])

	def convolve(self) -> Self:
		"Inverse of deconvolve: (a0 + a1) * (b0 + b1) -> a0*b0 + a0*b1 + a1*b0 + a1*b1"
		if self.type_ != ExpressionType.MULTIPLY:
			raise NotDeconvolvedFormError("Expression is not a MULTIPLY")

		left, right = self.operands
		if left.type_ != ExpressionType.ADD or right.type_ != ExpressionType.ADD:
			raise NotDeconvolvedFormError("Both operands must be ADD")

		# Expand the product: (a0 + a1) * (b0 + b1) = a0*b0 + a0*b1 + a1*b0 + a1*b1
		terms = []
		for a in left.operands:
			for b in right.operands:
				# Handle UNIT (e.g., 1 * x -> x)
				if a.type_ == ExpressionType.UNIT:
					terms.append(b)
				elif b.type_ == ExpressionType.UNIT:
					terms.append(a)
				else:
					terms.append(Expression(ExpressionType.MULTIPLY, [a, b]))

		return Expression(ExpressionType.ADD, terms)
	
	def __add__(self, other):
		try:
			return Expression(ExpressionType.ADD, [self, other]).flatten()
		except ValueError:
			return NotImplemented
	
	def __mul__(self, other):
		try:
			return Expression(ExpressionType.MULTIPLY, [self, other])
		except ValueError:
			return NotImplemented
	
	@classmethod
	def _const(cls, value):
		return Expression(ExpressionType.CONSTANT, [value])
	
	@classmethod
	def _var(cls, index):
		return Expression(ExpressionType.VARIABLE, [index])
	
	def is_subexpression(self, other: Self) -> bool:
		"Checks if the argument is a subexpression of self."
		if self == other:
			return True
		
		if self.type_ == ExpressionType.ADD or self.type_ == ExpressionType.MULTIPLY:
			return any(op.is_subexpression(other) for op in self.operands)
		
		return False
	
	def renumber_vars(self, renumbering):
		if self.type_ == ExpressionType.VARIABLE:
			try:
				n = renumbering[self.operands[0]]
			except (KeyError, IndexError):
				return self
			else:
				return Expression(self.type_, [n])
		elif self.type_ in {ExpressionType.ADD, ExpressionType.MULTIPLY}:
			return Expression(self.type_, [_expr.renumber_vars(renumbering) for _expr in self.operands])
		else:
			return self
	
	def variables(self):
		if self.type_ == ExpressionType.VARIABLE:
			yield self
		elif self.type_ in {ExpressionType.ADD, ExpressionType.MULTIPLY}:
			for operand in self.operands:
				yield from operand.variables()


def is_zero(expr: Expression) -> bool:
	"Checks if the expression is identically zero."
	return expr.type_ == ExpressionType.ZERO


def is_one(expr: Expression) -> bool:
	"Checks if the expression is identically one."
	return expr.type_ == ExpressionType.UNIT


def heuristic_transform(expr: Expression) -> Expression:
	"""
	Applies heuristic transformations to an expression:
	- Replaces with ZERO or UNIT if applicable.
	- Flattens nested additions.
	- Removes ZERO from additions.
	- Removes UNIT from multiplications.
	- Checks for multiplication by ZERO.
	- Deconvolves applicable multiplications.
	"""
	# First check for zero or one
	if is_zero(expr):
		return Expression(ExpressionType.ZERO, [])
	if is_one(expr):
		return Expression(ExpressionType.UNIT, [])

	# Keep applying transformations until none succeed
	while True:
		transformed = False
		new_expr = expr

		# Try to flatten additions
		if expr.type_ == ExpressionType.ADD:
			try:
				new_expr = expr.flatten()
				if new_expr != expr:
					expr = new_expr
					transformed = True
			except NotFlattenableError:
				pass

		# Try to remove zeros from additions
		if expr.type_ == ExpressionType.ADD and not transformed:
			try:
				new_expr = expr.remove_zero()
				if new_expr != expr:
					expr = new_expr
					transformed = True
			except NotZeroRemovableError:
				pass

		# Try to remove ones from multiplications
		if expr.type_ == ExpressionType.MULTIPLY and not transformed:
			try:
				new_expr = expr.remove_one()
				if new_expr != expr:
					expr = new_expr
					transformed = True
			except NotOneRemovableError:
				pass

		# Try to detect multiplication by zero
		if expr.type_ == ExpressionType.MULTIPLY and not transformed:
			try:
				new_expr = expr.zero_product()
				if new_expr != expr:
					expr = new_expr
					transformed = True
			except ExpressionError:
				pass

		# Try to deconvolve multiplications
		if expr.type_ == ExpressionType.ADD and not transformed:
			try:
				new_expr = expr.deconvolve()
				if new_expr != expr:
					expr = new_expr
					transformed = True
			except NotConvolvedFormError:
				pass

		# If no transformation succeeded, exit the loop
		if not transformed:
			break

	return expr


def to_linear(expr: Expression, right_list:List[Expression]) -> Expression:
	"""
	Converts an expression to linear form: const1 * var1 + const2 * var2 + ...
	If a free constant is found, it's converted to constant * input[0].
	If a free variable is found, it's converted to UNIT * variable.
	"""
	
	#print(expr)
	if expr.type_ == ExpressionType.CONSTANT:
		result = Expression(ExpressionType.MULTIPLY, [expr, Expression(ExpressionType.VARIABLE, [0])])
	
	elif expr.type_ == ExpressionType.VARIABLE:
		i = len(right_list)
		right_list.append(expr)
		result = Expression(ExpressionType.MULTIPLY, [Expression(ExpressionType.UNIT, []), Expression(ExpressionType.VARIABLE, [i])])
	
	elif expr.type_ == ExpressionType.ADD:
		operands = []
		for operand in expr.operands:
			ee = to_linear(operand, right_list)
			if ee.type_ == ExpressionType.ADD:
				operands.extend(ee.operands)
			else:
				operands.append(ee)
		result = Expression(ExpressionType.ADD, operands)
	
	elif expr.type_ == ExpressionType.MULTIPLY:
		# If it's already in linear form, return as is
		left, right = expr.operands
		left = to_linear(left, right_list)
		right = to_linear(right, right_list)
		if left.type_ in {ExpressionType.CONSTANT, ExpressionType.UNIT} and right.type_ == ExpressionType.VARIABLE:
			result = expr
		elif right.type_ in {ExpressionType.CONSTANT, ExpressionType.UNIT} and left.type_ == ExpressionType.VARIABLE:
			result = Expression(ExpressionType.MULTIPLY, [right, left])
		else:
			i = len(right_list)
			right_list.append(expr)
			result = Expression(ExpressionType.MULTIPLY, [Expression(ExpressionType.UNIT, []), Expression(ExpressionType.VARIABLE, [i])])
	
	else:
		result = expr
	
	assert is_linear(result), str(result)
	return result


def to_quadratic(expr: Expression, right_list:List[Expression]) -> Expression:
	"""
	Converts an expression to quadratic form: linear_expr * linear_expr
	If the input is linear, it's multiplied by (UNIT * input[0]) to make it quadratic.
	"""
	
	if expr.type_ == ExpressionType.MULTIPLY:
		# Already quadratic
		left, right = expr.operands
		left = to_linear(left, right_list)
		right = to_linear(right, right_list)
		result = Expression(ExpressionType.MULTIPLY, [left, right])
	
	else:
		# Convert to linear and multiply by (UNIT * input[0])
		linear_expr = to_linear(expr, right_list)
		unit_zero = Expression(ExpressionType.MULTIPLY, [Expression(ExpressionType.UNIT, []), Expression(ExpressionType.VARIABLE, [0])])
		result = Expression(ExpressionType.MULTIPLY, [linear_expr, unit_zero])
	
	assert is_quadratic(result)
	return result


def is_linear(expr: Expression) -> bool:
	"Checks if an expression is linear (constant × variable)."
	
	if expr.type_ == ExpressionType.MULTIPLY:
		left, right = expr.operands
		# Check if one operand is a constant or unit and the other is a variable
		if left.type_ in {ExpressionType.CONSTANT, ExpressionType.UNIT} and right.type_ == ExpressionType.VARIABLE:
			return True
	
	elif expr.type_ == ExpressionType.ADD:
		for subexpr in expr.operands:
			if subexpr.type_ == ExpressionType.MULTIPLY:
				left, right = subexpr.operands
				if left.type_ in {ExpressionType.CONSTANT, ExpressionType.UNIT} and right.type_ == ExpressionType.VARIABLE:
					pass
				else:
					return False
			else:
				return False
		else:
			return True
	
	return False


def is_quadratic(expr: Expression) -> bool:
	"Checks if an expression is quadratic (product of two linear expressions)."
	if expr.type_ != ExpressionType.MULTIPLY:
		return False
	
	left, right = expr.operands
	return is_linear(left) and is_linear(right)


def make_layer(expressions: List[Expression]) -> Tuple[List[Expression], List[Expression]]:
	"""
	Splits a list of expressions into two lists:
	- Left: Quadratic expressions (product of two linear expressions)
	- Right: Linear expressions (product of constant and variable)
	
	Always inserts input[0] as the first item of the right layer and ensures it stays there.
	"""
	left_list = []
	right_list = []
	
	# Always insert input[0] as the first item of the right layer
	right_list.append(Expression(ExpressionType.VARIABLE, [0]))
	
	# Always insert (UNIT * input['i']) * (UNIT * input['i']) as the first item of the left layer
	unit_zero = Expression(ExpressionType.VARIABLE, [0])
	unit_expr = Expression(ExpressionType.UNIT, [])
	linear_unit_zero = Expression(ExpressionType.MULTIPLY, [unit_expr, unit_zero])
	first_cell = Expression(ExpressionType.MULTIPLY, [linear_unit_zero, linear_unit_zero])
	left_list.append(first_cell)
	
	# Process each expression
	for expr in expressions:
		#print("make_layer", expr)
		# Try to deconvolve first
		try:
			expr = expr.deconvolve()
		except NotConvolvedFormError:
			pass
		
		if expr.type_ == ExpressionType.MULTIPLY:
			expr = to_quadratic(expr, right_list)
			left_list.append(expr)
		else:
			# If deconvolution fails, convert the expression to linear form
			expr = to_linear(expr, right_list)
			
			# Create a quadratic expression in the left list using the linear form directly
			expr = Expression(ExpressionType.MULTIPLY, [
				Expression(ExpressionType.MULTIPLY, [
					Expression(ExpressionType.UNIT, []),
					Expression(ExpressionType.VARIABLE, [0])
				]),
				expr
			])
			left_list.append(expr)
		old_right_list = right_list
	
	# Sort right list and make it unique.
	new_right_list = sorted(set(right_list))
	renumerate = {}
	for n, expr in enumerate(old_right_list):
		renumerate[n] = new_right_list.index(expr)
	right_list = new_right_list
	
	# Renumber variables in left list.
	old_new_list = left_list
	new_left_list = []
	for expr in left_list:
		new_left_list.append(expr.renumber_vars(renumerate))
	left_list = new_left_list
	
	# Make set of all variables from left list.
	variables = set()
	for expr in left_list:
		variables.update(expr.variables())
	
	# Remove unused entries from right list, preserving order.
	renumerate = {}
	old_right_list = right_list
	new_right_list = []
	for n in sorted(_v.operands[0] for _v in variables):
		if not isinstance(n, int): continue # don't touch final arguments
		renumerate[n] = len(new_right_list)
		new_right_list.append(old_right_list[n])
	right_list = new_right_list

	# Renumber variables in left list.
	old_new_list = left_list
	new_left_list = []
	for expr in left_list:
		new_left_list.append(expr.renumber_vars(renumerate))
	left_list = new_left_list
	
	# Verify that input[0] is the first item in the right layer
	assert right_list[0].type_ == ExpressionType.VARIABLE and right_list[0].operands[0] == 0
	
	# Verify that every item in the left list is a quadratic expression
	for i, expr in enumerate(left_list):
		assert is_quadratic(expr), f"Expression {expr} at position {i} is not quadratic"
	
	# Assert that the size of the left returned layer is equal to the length of the original argument plus one
	assert len(left_list) == len(expressions) + 1, f"Left layer size {len(left_list)} != {len(expressions) + 1}"
	
	# Assert that every item in the right list is a subexpression of one expression from the original argument
	for i, expr in enumerate(right_list[1:], 1):
		assert any(original_expr.is_subexpression(expr) for original_expr in expressions), f"Expression {expr} at index {i} is not a subexpression of any original expression"
	
	return left_list, right_list


def build_circuit(expressions: List[Expression]) -> List[List[Expression]]:
	"""
	Builds a circuit (list of layers) from a list of expressions.
	Each layer is a list of expressions, with the last layer containing only constants and variables.
	"""
	circuit = []
	current_layer = expressions
	
	while True:
		# Apply heuristic transform to each expression in the current layer
		#transformed_layer = [heuristic_transform(expr) for expr in current_layer]
		
		# Generate the next layer
		left_list, right_list = make_layer(current_layer)
		if not circuit:
			circuit.append(left_list[1:])
		else:
			circuit.append(left_list)
		
		#print([str(_x) for _x in left_list], [str(_x) for _x in right_list])
		
		# Check if the right list contains only constants, variables, and units
		if all(expr.type_ in {ExpressionType.CONSTANT, ExpressionType.VARIABLE, ExpressionType.UNIT, ExpressionType.ZERO} for expr in right_list):
			circuit.append(right_list)
			break
		
		current_layer = right_list[1:]
	
	return circuit


def calculate_area(circuit: List[List[Expression]]) -> int:
	"""
	Calculates the "area" of the circuit, defined as:
	(width of the widest layer) × (number of layers - 1)
	"""
	if not circuit:
		return 0
	max_width = max(len(layer) for layer in circuit)
	num_layers = len(circuit)
	return max_width * (num_layers - 1)


if __name__ == '__main__':
	x0 = Expression._var('x0')
	x1 = Expression._var('x1')
	x2 = Expression._var('x2')
	x3 = Expression._var('x3')
	
	a = Expression._const('a')
	b = Expression._const('b')
	c = Expression._const('c')
	d = Expression._const('d')
	
	f = (x0 * a + x0 * b + x0 * c + x1 * a + x1 * b + c * x1).deconvolve()
	g = x2 * c * d + x1 * x3 * x0
	h = (f * g) + a + x0
	
	print(f)
	print(g)
	print(h)
	print()
	
	#l, r = make_layer([g])
	#for x in l:
	#	print(x)
	#print()
	#for x in r:
	#	print(x)
	#print()
	
	#h = x0 * a * (b + c * x1)
	
	for layer in build_circuit([f, g, h]):
		for expr in layer:
			print(expr)
		print()





