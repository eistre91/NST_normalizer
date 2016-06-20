from pyparsing import *
from copy import deepcopy

"""
	Will attempt to normalize given lambda terms for NNST. 
	
	Syntax for Lambda Term Parsing:
		Lambdas are to be written as (Lx.M)    	['L', variable, expr]
		Application 							['A', expr, expr]
		Universal Quantification as U    		['U', L-var, expr]
		Pairing as P( , )   					['P', expr, expr]
		Pi0 or Pi1    							['Pi0'] | ['Pi1']
		Iota as I0(u) or I1(u)					['I0', expr] | ['I1', expr]
		Disjunction Elim as DE(x0.t0, x1.t1)	['DE', var, expr, var, expr]
		Existential intro as EI(m, u) 			['EI', L-var, expr]		
		Existential elim as EE((x,s).v)			['EE', L-var, var(?), expr]
		Membership as OUT(u) and IN(u)			['OUT', expr] | ['IN', expr]
		Equality introduction as EQ(_ ,_)		['EQ', expr, expr]
		Substitution as SUB(_, _)				['SUB', [expr, prop], [expr, equality]]
		
	Syntax for Logical Term Parsing:
		(logical_expr wedge logical_expr)		['wedge', logical_expr, logical_expr]
		(logical_expr rightarrow logical_expr)  ['rightarrow', _, _]
		forall x (logical_expr)					['forall', L-var, _]
		(logical_expr in logical_expr)			['in', _, _]
		(logical_expr equals logical_expr)		['equals', _, _]
		(logical_expr vee logical_expr)			['vee', _, _]
		exists x (logical_expr)					['exists', L-var, _]
		{x | logical_expr}						['set', L-var, logical_expr]
				

	Reduction Syntax:
		Lambda: 		['A', ['L', _, _], expr]
		Universal: 		['A', ['U', _, _], L-var]
		Conjunction:	['A', ['P', _, _], ['Pi0']]
		Disjunction: 	['A', ['I0', expr], ['DE', var, expr, var, expr]]
		Existential: 	['A', ['EI', L-var, expr], ['EE', L-var, expr, expr]]
		Membership: 	['OUT', ['IN', expr]]
		Equality: 
		
		
	BNF:
	
	lam :: 'L'
	var :: 'a'...'z'
	expr :: var | '(' expr expr ')' | '(' lam var . expr ')'

	To do:
	Unparsing for the complete lambda term language, up to needing parse/unparse for logical expr.
	Parsing for logical expressions.
	Unparsing for logical expressions.
	Determining if a variable is free in a parsed logical expression.
"""

var_list = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']
var = oneOf("a b c d e f g h i j k l m n o p q r s t u v w x y z")

lparen = Literal('(') #.suppress()
rparen = Literal(')') #.suppress()
lparens = Literal('(').suppress()
rparens = Literal(')').suppress()
#langle = Literal('<').suppress()
#rangle = Literal('>').suppress()
comma = Literal(',').suppress()

dot = Literal(".").suppress()
colon = Literal(":").suppress()

expr = Forward()

lam = Literal('L')

uni = Literal('U')

pair = Literal('P')
pi0 = Literal('Pi0')
pi1 = Literal('Pi1')

i0 = Literal('I0')
i1 = Literal('I1')
de = Literal('DE')

ei = Literal('EI')
ee = Literal('EE')

mout = Literal('OUT')
min = Literal('IN')

eq = Literal('EQ')
sub = Literal('SUB')

# logical parsing
# to suffice for the reduction rules for sub and eq, the cases to cover are
# x not free in A
# wedge
# rightarrow
# forall
# t(x) in {z | B(z, x)}
# t in x 
	# (x not free in t)
# t(x) in x 
	# (x free in t)
# t(x) in z
	# nothing to do in the event of this form
	# implicit non-normal
# t(x) = u(x)
# vee
# exists

logical_expr = Forward()

# Logical variables lists
L-var_list = ['la', 'lb', 'lc', 'ld', 'le', 'lf', 'lg', 'lh', 'li', 'lj', 'lk', 'll', 'lm', 'ln', 'lo', 'lp', 'lq', 'lr', 'ls', 'lt', 'lu', 'lv', 'lw', 'lx', 'ly', 'lz']
L-var = oneOf("la lb lc ld le lf lg lh li lj lk ll lm ln lo lp lq lr ls lt lu lv lw lx ly lz")

wedge = Literal('wedge').suppress()
vee = Literal('vee').suppress()
rightarrow = Literal('rightarrow').suppress()
exists = Literal('exists')
forall = Literal('forall')
equals = Literal('=').suppress()
member = Literal('in').suppress()
lbrace = Literal('{').suppress()
rbrace = Literal('}').suppress()
pipe = Literal('|').suppress()

def rearrange_action(x, connective):
	return x[0].remove(connective).insert(0,connective)

logical_expr << ( \
				L-var | \
				# (logical_expr wedge logical_expr)
				Group( lparens + logical_expr + wedge + logical_expr + rparens ).setParseAction(rearrange(x, 'wedge')) | \
				# (logical_expr rightarrow logical_expr)
				Group( lparens + logical_expr + rightarrow + logical_expr + rparens ).setParseAction(rearrange(x, 'rightarrow')) | \
				# forall x (logical_expr)
				Group( forall + L-var + lparens + logical_expr + rparens ) | \
				# (logical_expr in logical_expr)
				Group( lparens + logical_expr + member + logical_expr + rparens ).setParseAction(rearrange(x, 'member')) | \
				# (logical_expr equals logical_expr)
				Group( lparens + logical_expr + equals + logical_expr + rparens ).setParseAction(rearrange(x, 'equals')) | \				
				# (logical_expr vee logical_expr)
				Group( lparens + logical_expr + vee + logical_expr + rparens ).setParseAction(rearrange(x, 'vee')) | \
				# exists x (logical_expr)
				Group( exists + L-var + lparens + logical_expr + rparens ) | \
				# {x | logical_expr}
				Group( lbrace + L-var + pipe + logical_expr + rbrace ).setParseAction(lambda x: x[0].insert(0,'set')) 
				)
				
def has_free_occurrence_in(var, logical_expr):
	pass
	#assume false then
	#return (recursive_call) or (recursive_call)
	#returns true if it hits the variable
	#if it finds a binder of that variable, then the call ends
	#and it returns false for that sub-formula
	#the truth of any free occurrence will then propagate up 
	
expr << ( \
		var | \
		# (expr expr)
		Group(lparens + expr + expr + rparens).setParseAction(lambda x: x[0].insert(0,'A')) | \
		# (Lx.expr)
		Group( lparens + lam + var + dot + expr + rparens ) | \
		# (Ux.expr)
		Group( lparens + uni + var + dot + expr + rparens ) | \
		# P(expr, expr)
		Group( pair + lparens + expr + comma + expr + rparens ) | \
		# Pi0 
		Group( pi0 ) | \
		Group( pi1 ) | \
		# I0(expr)
		Group( i0 + lparens + expr + rparens ) | \
		Group( i1 + lparens + expr + rparens ) | \
		#DE(x0.t0, x1.t1)
		Group( de + lparens + var + dot + expr + comma + var + dot + expr + rparens ) | \
		#EI(m, u)
		Group( ei + lparens + var + comma + expr + rparens ) | \
		#EE((x, s).v)
		Group( ee + lparens + lparens + var + comma + var + rparens + dot + expr + rparens ) | \
		#OUT(u)
		Group( mout + lparens + expr + rparens ) | \
		#IN(u)
		Group( min + lparens + expr + rparens ) | \
		#EQ(x1.t1, x2.t2)
		Group( eq + lparens + var + dot + expr + comma + var + dot + expr + rparens ) | \
		#SUB(expr : logical_expr , expr : s = r)
		Group( sub + lparens + expr + colon + logical_expr + comma + expr + colon + logical_expr + rparens )
		)


# Unparses expressions and returns the string representation
# Takes in the full parsed expression list at index 0
def unparse(parsed_expr):
	expr_string = ""
	#if not isinstance(parsed_expr, list):
	if parsed_expr in var_list:
		expr_string = parsed_expr
	elif parsed_expr[0] == 'A': # ['A', expr, expr]
		expr_string = '(' + unparse(parsed_expr[1]) + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'L': # ['L', variable, expr]
		expr_string = '(' + 'L' + parsed_expr[1] + '.' + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'U': # ['U', L-var, expr]
		expr_string = '(' + 'U' + parsed_expr[1] + '.' + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'P': # ['P', expr, expr]
	    expr_string = 'P' + '(' + unparse(parsed_expr[1]) + ', ' + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'Pi0' or parsed_expr[0] == 'Pi1': # ['Pi0'] | ['Pi1']
	    expr_string = parsed_expr[0]
	elif parsed_expr[0] == 'I0' or parsed_expr[0] == 'I1': # ['I0', expr] | ['I1', expr]
	    expr_string = parsed_expr[0] + '(' + unparse(parsed_expr[1]) + ')'
	elif parsed_expr[0] == 'DE': # ['DE', var, expr, var, expr]
	    expr_string = 'DE' + '(' + parsed_expr[1] + '.' + unparse(parsed_expr[2]) + ', ' + parsed_expr[3] + '.' + unparse(parsed_expr[4]) + ')'
	elif parsed_expr[0] == 'EI': # ['EI', L-var, expr]	
	    expr_string = 'EI' + '(' + parsed_expr[1] + ', ' + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'EE': # ['EE', L-var, var, expr]
	    expr_string = 'EE' + '(' + '(' + parsed_expr[1] + ', ' + parsed_expr[2] + ')' + '.' + unparse(parsed_expr[3]) + ')'
	elif parsed_expr[0] == 'OUT' | parsed_expr[0] == 'IN': # ['OUT', expr] | ['IN', expr]
	    expr_String = parsed_expr[0] + '(' + unparse(parsed_expr[1]) + ')'
	elif parsed_expr[0] == 'EQ': # ['EQ', expr, expr]
	    expr_string = 'EQ' + '(' + unparse(parsed_expr[1]) + ', ' + unparsed(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'SUB': # ['SUB', [expr, prop], [expr, equality]]
	    expr_string = 'SUB' + '(' + unparse(parsed_expr[1][0]) + ':' + unparse_logical(parsed_expr[1][1]) + ', ' + unparse(parsed_expr[2][0]) + ':' + unparse_logical(parsed_expr[2][1]) + ')'
	return expr_string
	
def unparse_logical(parsed_expr):
	pass
	
#print(' '.join(expr.parseString('(ab)').asList()[0]))

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
	

# Lambda Reduction: ['A', ['L', var, expr0], expr1]
# Reduces to: expr1 subbed for all occurrences of var in expr0	
# Algorithm: traverse expr0 and find all occurrences of var and replace with expr1
def check_lambda_reduction(parsed_expr):
	if parsed_expr[0] == 'A' and parsed_expr[1][0] == 'L':
		return True
	else:
		return False
		
# Universal:	['A', ['U', _, _], L-var]
def check_universal_reduction(parsed_expr):
	if parsed_expr[0] == 'A' and parsed_expr[1][0] == 'U':
		return True
	else:
		return False
		
# Conjunction:	['A', ['P', _, _], ['Pi0']]
def check_conjunction0_reduction(parsed_expr):
	if parsed_expr[0] == 'A' and parsed_expr[1][0] == 'P' and parsed_expr[2][0] == 'Pi0':
		return True
	else:
		return False
		
# Conjunction:	['A', ['P', _, _], ['Pi1']]
def check_conjunction1_reduction(parsed_expr):
	if parsed_expr[0] == 'A' and parsed_expr[1][0] == 'P' and parsed_expr[2][0] == 'Pi1':
		return True
	else:
		return False
		
# Disjunction: 	['A', ['I0', expr], ['DE', var, expr, var, expr]]
def check_disjunction0_reduction(parsed_expr):
	if parsed_expr[0] == 'A' and parsed_expr[1][0] == 'I0' and parsed_expr[2][0] == 'DE':
		return True
	else:
		return False
		
# Disjunction: 	['A', ['I1', expr], ['DE', var, expr, var, expr]]
def check_disjunction1_reduction(parsed_expr):
	if parsed_expr[0] == 'A' and parsed_expr[1][0] == 'I1' and parsed_expr[2][0] == 'DE':
		return True
	else:
		return False
		
# Existential: 	['A', ['EI', L-var, expr], ['EE', L-var, expr, expr]]
def check_existential_reduction(parsed_expr):
	if parsed_expr[0] == 'A' and parsed_expr[1][0] == 'EI' and parsed_expr[2][0] == 'EE':
		return True
	else:
		return False
		
# Membership: 	['out', ['in', expr]]
def check_membership_reduction(parsed_expr):
	if parsed_expr[0] == 'OUT' and parsed_expr[1][0] == 'IN':
		return True
	else:
		return False
		
# Traverse the parsed expression and find a reduction
# Can't guarantee much about what order this algorithm proceeds, 
# but it will find all reductions
def find_reduction(parsed_expr):
	"""If you find reduction at the top level, do that one.
	Else go looking until you find one in a subtree, or reach a var."""
	result = []
	if parsed_expr in var_list:
		return parsed_expr
	elif check_lambda_reduction(parsed_expr):
		var = parsed_expr[1][1]
		primary_expr = parsed_expr[1][2]
		secondary_expr = parsed_expr[2]
		result = substitute(var, primary_expr, secondary_expr)		
		return result
	elif check_conjunction0_reduction(parsed_expr):
		#Conjunction:	['A', ['P', _, _], ['Pi0']]
		result = parsed_expr[1][1]
		return result
	elif check_conjunction1_reduction(parsed_expr):
		#Conjunction:	['A', ['P', _, _], ['Pi1']]
		result = parsed_expr[1][2]
		return result
	elif check_disjunction0_reduction(parsed_expr):
		#Disjunction: 	['A', ['I0', expr], ['DE', var, expr, var, expr]]
		var = parsed_expr[2][1]
		primary_expr = parsed_expr[2][2]
		secondary_expr = parsed_expr[1][1]
		result = substitute(var, primary_expr, secondary_expr)
		return result
	elif check_disjunction1_reduction(parsed_expr):
		#Disjunction: 	['A', ['I1', expr], ['DE', var, expr, var, expr]]
		var = parsed_expr[2][3]
		primary_expr = parsed_expr[2][4]
		secondary_expr = parsed_expr[1][1]
		result = substitute(var, primary_expr, secondary_expr)
		return result
	elif check_existential_reduction(parsed_expr):
		#Existential: 	['A', ['EI', L-var, expr], ['EE', L-var, var, expr]]
		first_var = parsed_expr[2][1]
		primary_expr = parsed_expr[2][3]
		first_secondary_expr = parsed_expr[1][1]
		second_var = parsed_expr[2][2]
		second_secondary_expr = parsed_expr[1][2]
		result = substitute(first_var, primary_expr, first_secondary_expr)
		result = substitute(second_var, result, second_secondary_expr)
		return result
	elif check_membership_reduction(parsed_expr):
		#Membership: 	['OUT', ['IN', expr]]
		result = parsed_expr[1][1]
		return result
	elif check_universal_reduction(parsed_expr):
		#Universal: 		['A', ['U', _, _], L-var]
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
		elif parsed_expr[0] == 'P':
			result = ['P', find_reduction(parsed_expr[1]), find_reduction(parsed_expr[2])]
			return result
		elif parsed_expr[0] == 'U':
			result = ['U', parsed_expr[1], find_reduction(parsed_expr[2])]
			return result 
		elif parsed_expr[0] == 'Pi0' or parsed_expr[0] == 'Pi1':
			return parsed_expr
		elif parsed_expr[0] == 'I0' or parsed_expr[0] == 'I1':
			result = [parsed_expr[0], find_reduction(parsed_expr[1])]
			return result
		elif parsed_expr[0] == 'DE':
			result = ['DE', parsed_expr[1], find_reduction(parsed_expr[2]), parsed_expr[3], find_reduction(parsed_expr[4])]
			return result
		elif parsed_expr[0] == 'EI':
			result = ['EI', parsed_expr[1], find_reduction(parsed_expr[2])]
			return result
		elif parsed_expr[0] == 'EE':
			result = ['EE', parsed_expr[1], parsed_expr[2], find_reduction(parsed_expr[3])]
			return result
		elif parsed_expr[0] == 'OUT' or parsed_expr[0] == 'IN':
			result = [parsed_expr[0], find_reduction(parsed_expr[1])]
			return result
		else:
			return parsed_expr
			
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
	#reduction_result = step_reduce(test_parse[0].asList())
	#print(reduction_result)
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
	#reduction_result = step_reduce(test_parse[0].asList())
	#print(reduction_result)
	normalize_result = normalize(test_parse[0].asList())
	print(normalize_result)
	print(unparse(normalize_result))
	print()
	
	print(expr.parseString('Pi0'))
	
	#Does white space matter?
		#white space ignored by default in pyparser
	
	#Lambda: 		['A', ['L', _, _], expr]
	#Universal: 	['A', ['U', _, _], L-var]
	#Conjunction:	['A', ['P', _, _], ['Pi0']]
	#Disjunction: 	['A', ['I0', expr], ['DE', var, expr, var, expr]]
	#Existential: 	['A', ['EI', L-var, expr], ['EE', L-var, expr, expr]]
	#Membership: 	['OUT', ['IN', expr]]

	
# Couldn't figure out how to make results names work.

# <---------- Old Code ---------->

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
