from pyparsing import *
from copy import deepcopy

"""
	Will attempt to normalize given lambda terms for NNST. 
	
	Syntax:
		Lambdas are to be written as (Lx.M)    		['L', variable, expr]
		Application 							['A', expr, expr]
		
		Universal Quantification as U    		['U', L-var, expr]
		Pairing as P< _, _ >    				['P', expr, expr]
		Pi0 or Pi1    							['Pi0'] | ['Pi1']
		Iota as I0(u) or I1(u)					['I0', expr] | ['I1', expr]
		Disjunction Elim as DE(x1.t1, x2.t2)	['DE', expr, expr, expr, expr]
		Existential intro as EI(m, u) 			['EI', L-var, expr]		
		Existential elim as EE((x,s).v)			['EE', L-var, expr, expr]
		Membership as out(u) and in(u)			['out', expr] | ['in', expr]
		Equality introduction as eq(_ ,_)		['eq', expr, expr]
		Substitution as sub(_, _)				['sub', [expr, prop], [expr, equality]]

	Reduction Syntax:
		Lambda: 		['A', ['L', _, _], expr]
		Universal: 		['A', ['U', _, _], L-var]
		Conjunction:	['A', ['P', _, _], ['Pi0']]
		Disjunction: 	['A', ['I0', expr], ['DE', expr, expr, expr, expr]]
		Existential: 	['A', ['EI', L-var, expr], ['EE', L-var, expr, expr]]
		Membership: 	['out', ['in', expr]]
		Equality: 
		
		
	BNF:
	
	lam :: 'L'
	var :: 'a'...'z'
	expr :: var | '(' expr expr ')' | '(' lam var . expr ')'
"""

expr = Forward()

lam = Literal('L')
var = oneOf("a b c d e f g h i j k l m n o p q r s t u v w x y z")
lparen = Literal('(') #.suppress()
rparen = Literal(')') #.suppress()
lparens = Literal('(').suppress()
rparens = Literal(')').suppress()
dot = Literal(".")

#expr << var

#application = lparen + expr + expr + rparen

expr << ( \
		var | \
		Group(lparens + expr + expr + rparens).setParseAction(lambda x: x[0].insert(0,'A')) | \
		lparens + Group( lam + var + dot.suppress() + expr ) + rparens
		)
		
#Group(lparens + expr + expr + rparens).setParseAction(lambda x: x[0].insert(0,'A')) | \



# Unparses expressions and returns the string representation
# Takes in the full parsed expression list at index 0
def unparse(parsed_expr):
	expr_string = ""
	if not isinstance(parsed_expr, list):
		expr_string = parsed_expr
	elif parsed_expr[0] == 'A':
		expr_string = '(' + unparse(parsed_expr[1]) + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'L':
		expr_string = '(' + 'L' + parsed_expr[1] + '.' + unparse(parsed_expr[2]) + ')'
	return expr_string
#print(' '.join(expr.parseString('(ab)').asList()[0]))

#Lambda Reduction: ['A', ['L', var, expr0], expr1]
#Reduces to: expr1 subbed for all occurrences of var in expr0	
#Algorithm: traverse expr0 and find all occurrences of var and replace with expr1
def check_lambda_reduction(parsed_expr):
	if parsed_expr[0] == 'A' and parsed_expr[1][0] == 'L':
		return True

# Takes in the full parsed expression list at index 0	
# Will perform a single reduction step at the first reduction it finds
def step_reduce(parsed_expr):
	'''Check to see if a reduction can be performed at the current level
		If so, do it 
		Return reduced expr as parsed list'''
	result = []
	
	if check_lambda_reduction(parsed_expr):
		var = parsed_expr[1][1]
		primary_expr = parsed_expr[1][2]
		secondary_expr = parsed_expr[2]
		result = substitute(var, primary_expr, secondary_expr)
	
	return result

# Traverse the parsed expression and find a reduction
# Can't guarantee much about what order this algorithm proceeds, 
# but it will find all reductions
def find_reduction(parsed_expr):
	"""If you find reduction at the top level, do that one.
	Else go looking until you find one in a subtree, or reach a var."""
	result = []
	if isinstance(parsed_expr, str):
		return parsed_expr
	elif check_lambda_reduction(parsed_expr):
		var = parsed_expr[1][1]
		primary_expr = parsed_expr[1][2]
		secondary_expr = parsed_expr[2]
		result = substitute(var, primary_expr, secondary_expr)		
		return result
	else: 
		if parsed_expr[0] == 'A':
			result = ['A', find_reduction(parsed_expr[1]), find_reduction(parsed_expr[2])]
			return result
		elif parsed_expr[0] == 'L':
			result = ['L', var, find_reduction(parsed_expr[2])]
			return result
		else:
			return parsedExpr
			
def normalize(parsed_expr, max_iterations = 100):
	iterations = 1
	pre_reduced = parsed_expr
	reduced = find_reduction(parsed_expr)
	print("Iteration:", iterations, "\n current expression:", reduced)
	while iterations < max_iterations and pre_reduced != reduced:
		pre_reduced = reduced
		reduced = find_reduction(reduced)
		iterations += 1
		print("Iteration:", iterations, "\n current expression:", reduced)
	return reduced
	
# Traverse the parsed expression to find all instances of var
# in primary expr to be replaced by secondary_expr
def substitute(var, primary_expr, secondary_expr):
	result = None
	if primary_expr == var:
		result = secondary_expr
	elif isinstance(primary_expr, list):
		result = deepcopy(primary_expr)
		for i, piece in enumerate(primary_expr):
			if piece == var:
				result[i] = secondary_expr
			elif isinstance(piece, list):
				result[i] = substitute(var, piece, secondary_expr)
			else:
				pass
	else: 
		pass
	return result
	
# This is definitely not the most efficient program 
# possible due to re-scanning and many many other redundancies.

# Test code
if __name__ == "__main__":
	print()

	print(expr.parseString('a'))
	print()
	
	test_string = '(ab)'
	test_parse = expr.parseString(test_string)
	print(test_parse)
	print(unparse(test_parse[0].asList()))
	print()
	
	test_string = '(Lx.x)'
	test_parse = expr.parseString(test_string)
	print(test_parse)
	print(unparse(test_parse[0].asList()))
	print()
	
	print(expr.parseString('(Lx.((ab)(cd)))'))
	print(expr.parseString('((Lx.x)(Ly.y))'))
	print(expr.parseString('(((Lx.(Lz.z))(Ly.y))(Lx.x))'))
	print()
	
	test_string = '(((Lx.(Lz.(La.a)))(Ly.y))((Lx.x)(Lb.b)))'
	test_parse = expr.parseString(test_string)
	print(test_parse)
	print(unparse(test_parse[0].asList()) == test_string)
	print()
	
	test_string = '((Lx.x)y)'
	test_parse = expr.parseString(test_string)
	print(test_parse)
	reduction_result = step_reduce(test_parse[0].asList())
	print(reduction_result)
	reduction_result = find_reduction(test_parse[0].asList())
	print(reduction_result)
	print()
	
	test_string = '(((Ly.(Lx.(xy)))a)b)'
	test_parse = expr.parseString(test_string)
	print(test_parse)
	#reduction_result = step_reduce(test_parse[0].asList())
	#print(reduction_result)
	reduction_result = find_reduction(test_parse[0].asList())
	print(reduction_result)
	reduction_result = normalize(test_parse[0].asList())
	print(reduction_result)
	print()
	
	test_string = '((Lx.((xx)(cd)))(Ly.y))'
	test_parse = expr.parseString(test_string)
	print(test_parse)
	test_string_reduced = '(((Ly.y)(Ly.y))(cd))'
	test_parse_reduced = expr.parseString(test_string_reduced)
	print(test_parse_reduced)
	reduction_result = step_reduce(test_parse[0].asList())
	print(reduction_result)
	normalize_result = normalize(test_parse[0].asList())
	print(normalize_result)
	print(unparse(reduction_result))
	print(unparse(normalize_result))
	print()

	
# Couldn't figure out how to make results names work.