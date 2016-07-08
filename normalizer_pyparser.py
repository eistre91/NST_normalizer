from pyparsing import *
from copy import deepcopy

"""
	Will attempt to normalize given lambda terms for NNST. 
	
	Syntax for Lambda Term Parsing:
		Lambdas are to be written as (Lx.M)    	['L', variable, expr]
		Application 							['A', expr, expr]
		Universal Quantification as U    		['U', L_var, expr]
		Pairing as P( , )   					['P', expr, expr]
		Pi0 or Pi1    							['Pi0'] | ['Pi1']
		Iota as I0(u) or I1(u)					['I0', expr] | ['I1', expr]
		Disjunction Elim as DE(x0.t0, x1.t1)	['DE', var, expr, var, expr]
		Existential intro as EI(m, u) 			['EI', L_var, expr]		
		Existential elim as EE((x,s).v)			['EE', L_var, var(?), expr]
		Membership as OUT(u) and IN(u)			['OUT', expr] | ['IN', expr]
		Equality introduction as EQ(_ ,_)		['EQ', expr, expr]
		Substitution_0 as SUB0(_, _)			['SUB0', expr, prop, expr, equality]
		Substitution_1 as SUB1(_, _)			['SUB1', expr, prop, expr, equality]

		
	Syntax for Logical Term Parsing:
		(logical_expr wedge logical_expr)		['wedge', logical_expr, logical_expr]
		(logical_expr rightarrow logical_expr)  ['rightarrow', _, _]
		forall x (logical_expr)					['forall', L_var, _]
		(logical_expr in logical_expr)			['in', _, _]
		(logical_expr equals logical_expr)		['equals', _, _]
		(logical_expr vee logical_expr)			['vee', _, _]
		exists x (logical_expr)					['exists', L_var, _]
		{x | logical_expr}						['set', L_var, logical_expr]
				

	Reduction Syntax:
		Lambda: 		['A', ['L', _, _], expr]
		Universal: 		['A', ['U', _, _], L_var]
		Conjunction:	['A', ['P', _, _], ['Pi0']]
		Disjunction: 	['A', ['I0', expr], ['DE', var, expr, var, expr]]
		Existential: 	['A', ['EI', L_var, expr], ['EE', L_var, expr, expr]]
		Membership: 	['OUT', ['IN', expr]]
		Equality: 		['SUB', expr, prop, ['EQ', expr, expr], equality]				

		
		
	BNF:
	
	lam :: 'L'
	var :: 'a'...'z'
	expr :: var | '(' expr expr ')' | '(' lam var . expr ')'

	To do:
	Need to test: Unparsing for the complete lambda term language, up to needing parse/unparse for logical expr.
	Need to test: Parsing for logical expressions.
	Need to test: Unparsing for logical expressions.
	Need to test: Determining if a variable is free in a parsed logical expression.
	Finish reduction rules by adding rules for eq/sub.
		Revealed problems: Substitute function will need to work for non atomic variables.
									Wait no, I don't actually have to perform the substitution.
									Well sorta, I need to determine what's free in the logical expression.
									And to do that do I need to substitute x for s and test x for freeness...or can I test s for freeness? 
									Even though that's not atomic.
									I think I literally just have to see there are no occurences of s...because s wouldn't be bound anyway.
									Unless s was being used in multiple places, or we replace it with x and x was in multiple places...but then it has multiple meanings.
									And so I don't have to care about the other ones. 
									Enforcing "fresh variables". If x is bound in some part of the logical expression, then x's only occur inside that. 
									The first reduction rule then becomes: If the thing your subbing for doesn't actually occur, then you didn't need to have subbed.
	Universal reduction should work for any term of the logical language, not just variables. It remains though that I don't understand when this wouldn't be possible.
		i.e. I can ignore universal in the lambda calculus. If a term doesn't finish reducing, it's not due to universal.
"""
used_variables = []
	
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
sub0 = Literal('SUB0')
sub1 = Literal('SUB1')

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
L_var_list = ['la', 'lb', 'lc', 'ld', 'le', 'lf', 'lg', 'lh', 'li', 'lj', 'lk', 'll', 'lm', 'ln', 'lo', 'lp', 'lq', 'lr', 'ls', 'lt', 'lu', 'lv', 'lw', 'lx', 'ly', 'lz']
L_var = oneOf("la lb lc ld le lf lg lh li lj lk ll lm ln lo lp lq lr ls lt lu lv lw lx ly lz")

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

def rearrange(x, connective):
	return x[0].insert(0,connective)

logical_expr << ( \
				L_var | \
				# (logical_expr wedge logical_expr)
				Group( lparens + logical_expr + wedge + logical_expr + rparens ).setParseAction(lambda x: rearrange(x, 'wedge')) | \
				# (logical_expr rightarrow logical_expr)
				Group( lparens + logical_expr + rightarrow + logical_expr + rparens ).setParseAction(lambda x: rearrange(x, 'rightarrow')) | \
				# forall x (logical_expr)
				Group( forall + L_var + lparens + logical_expr + rparens ) | \
				# (logical_expr in logical_expr)
				Group( lparens + logical_expr + member + logical_expr + rparens ).setParseAction(lambda x: rearrange(x, 'in')) | \
				# (logical_expr = logical_expr)
				Group( lparens + logical_expr + equals + logical_expr + rparens ).setParseAction(lambda x: rearrange(x, '=')) | \
				# (logical_expr vee logical_expr)
				Group( lparens + logical_expr + vee + logical_expr + rparens ).setParseAction(lambda x: rearrange(x, 'vee')) | \
				# exists x (logical_expr)
				Group( exists + L_var + lparens + logical_expr + rparens ) | \
				# {x | logical_expr}
				Group( lbrace + L_var + pipe + logical_expr + rbrace ).setParseAction(lambda x: x[0].insert(0,'set')) 
				)
				
# Binders:
	# forall
	# exists
	# {x | logical_expr}	

# Syntax: 
	# L_var 
	# (logical_expr wedge logical_expr)		['wedge', logical_expr, logical_expr]
	# (logical_expr rightarrow logical_expr)  ['rightarrow', _, _]
	# forall x (logical_expr)					['forall', L_var, _]
	# (logical_expr in logical_expr)			['in', _, _]
	# (logical_expr equals logical_expr)		['equals', _, _]
	# (logical_expr vee logical_expr)			['vee', _, _]
	# exists x (logical_expr)					['exists', L_var, _]
	# {x | logical_expr}						['set', L_var, logical_expr]

# For use with parsed logical expressions	
def has_free_occurrence_in(var, parsed_expr):
	#assume false then
	#return (recursive_call) or (recursive_call)
	#returns true if it hits the variable
	#if it finds a binder of that variable, then the call ends
	#and it returns false for that sub-formula
	#the truth of any free occurrence will then propagate up 
	free_occurrence = False
	if parsed_expr == var:
		free_occurrence = True
	elif parsed_expr[0] in ['wedge', 'rightarrow', 'in', '=', 'vee']:
		free_occurrence = has_free_occurrence_in(var, parsed_expr[1]) or has_free_occurrence_in(var, parsed_expr[2])
	elif parsed_expr[0] in ['forall', 'exists', 'set']:
		if parsed_expr[1] == var: # the variable is bound in the subexpression
			free_occurrence = False
		else:
			free_occurrence = has_free_occurrence_in(var, parsed_expr[2])
	elif parsed_expr in L_var_list: #if it gets there, didn't find the variable unbound or bound
		free_occurrence = False
	return free_occurrence
	
def is_subformula_of(parsed_subformula, parsed_expr):
	is_subformula = False
	if parsed_expr == parsed_subformula:
		is_subformula = True
	elif parsed_expr[0] in ['wedge', 'rightarrow', 'in', '=', 'vee']:
		is_subformula = is_subformula_of(parsed_subformula, parsed_expr[1]) or is_subformula_of(parsed_subformula, parsed_expr[2])
	elif parsed_expr[0] in ['forall', 'exists', 'set']:
		is_subformula = is_subformula_of(parsed_subformula, parsed_expr[2])
	return is_subformula
	
def replace_subformula(parsed_expr, replaced, replacer):
	result = parsed_expr
	if parsed_expr == replaced:
		result = replacer
	elif parsed_expr[0] in ['wedge', 'rightarrow', 'in', '=', 'vee']:
		result = [parsed_expr[0], replace_subformula(parsed_expr[1], replaced, replacer), replace_subformula(parsed_expr[2], replaced, replacer)]
	elif parsed_expr[0] in ['forall', 'exists', 'set']:
		result = [parsed_expr[0], parsed_expr[1], replace_subformula(parsed_expr[2], replaced, replacer)]
	return result
	
expr << ( \
		var.setParseAction(lambda x: used_variables.append(x)) | \
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
		#Group( eq + lparens + var + dot + expr + comma + var + dot + expr + rparens ) | \
		#EQ(expr, expr)
		Group ( eq + lparens + expr + comma + expr + rparens ) | \
		#SUB(expr : logical_expr , expr : s = r)
		Group( sub0 + lparens + expr + colon + logical_expr + comma + expr + colon + logical_expr + rparens ) | \
		Group( sub1 + lparens + expr + colon + logical_expr + comma + expr + colon + logical_expr + rparens ) 
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
	elif parsed_expr[0] == 'U': # ['U', L_var, expr]
		expr_string = '(' + 'U' + parsed_expr[1] + '.' + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'P': # ['P', expr, expr]
	    expr_string = 'P' + '(' + unparse(parsed_expr[1]) + ', ' + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'Pi0' or parsed_expr[0] == 'Pi1': # ['Pi0'] | ['Pi1']
	    expr_string = parsed_expr[0]
	elif parsed_expr[0] == 'I0' or parsed_expr[0] == 'I1': # ['I0', expr] | ['I1', expr]
	    expr_string = parsed_expr[0] + '(' + unparse(parsed_expr[1]) + ')'
	elif parsed_expr[0] == 'DE': # ['DE', var, expr, var, expr]
	    expr_string = 'DE' + '(' + parsed_expr[1] + '.' + unparse(parsed_expr[2]) + ', ' + parsed_expr[3] + '.' + unparse(parsed_expr[4]) + ')'
	elif parsed_expr[0] == 'EI': # ['EI', L_var, expr]	
	    expr_string = 'EI' + '(' + parsed_expr[1] + ', ' + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'EE': # ['EE', L_var, var, expr]
	    expr_string = 'EE' + '(' + '(' + parsed_expr[1] + ', ' + parsed_expr[2] + ')' + '.' + unparse(parsed_expr[3]) + ')'
	elif parsed_expr[0] == 'OUT' or parsed_expr[0] == 'IN': # ['OUT', expr] | ['IN', expr]
	    expr_string = parsed_expr[0] + '(' + unparse(parsed_expr[1]) + ')'
	elif parsed_expr[0] == 'EQ': # ['EQ', expr, expr]
	    expr_string = 'EQ' + '(' + unparse(parsed_expr[1]) + ', ' + unparse(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'SUB0' or parsed_expr[0] == 'SUB1': # ['SUB', expr, prop, expr, equality]
	    expr_string = parsed_expr[0] + '(' + unparse(parsed_expr[1]) + ':' + unparse_logical(parsed_expr[2]) + ', ' + unparse(parsed_expr[3]) + ':' + unparse_logical(parsed_expr[4]) + ')'
	return expr_string
	
#	Syntax for Logical Term Parsing:
#		(logical_expr wedge logical_expr)		['wedge', logical_expr, logical_expr]
#		(logical_expr rightarrow logical_expr)  ['rightarrow', _, _]
#		forall x (logical_expr)					['forall', L_var, _]
#		(logical_expr in logical_expr)			['in', _, _]
#		(logical_expr equals logical_expr)		['equals', _, _]
#		(logical_expr vee logical_expr)			['vee', _, _]
#		exists x (logical_expr)					['exists', L_var, _]
#		{x | logical_expr}						['set', L_var, logical_expr]
	
def unparse_logical(parsed_expr):
	expr_string = ""
	if parsed_expr in L_var_list:
		expr_string = parsed_expr
	elif parsed_expr[0] == 'wedge': #['wedge', logical_expr, logical_expr]
		expr_string = '(' + unparse_logical(parsed_expr[1]) + ' wedge ' + unparse_logical(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'rightarrow': #['rightarrow', _, _]
		expr_string = '(' + unparse_logical(parsed_expr[1]) + ' rightarrow ' + unparse_logical(parsed_expr[2]) + ')'	
	elif parsed_expr[0] == 'forall': #['forall', L_var, _]
		expr_string = 'forall ' + parsed_expr[1] + '(' + unparse_logical(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'in': #['in', _, _]
		expr_string = '(' + unparse_logical(parsed_expr[1]) + ' in ' + unparse_logical(parsed_expr[2]) + ')'
	elif parsed_expr[0] == '=': #['=', _, _]
		expr_string = '(' + unparse_logical(parsed_expr[1]) + ' = ' + unparse_logical(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'vee': #['vee', _, _]
		expr_string = '(' + unparse_logical(parsed_expr[1]) + ' vee ' + unparse_logical(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'exists': #['exists', L_var, _]
		expr_string = 'exists ' + parsed_expr[1] + '(' + unparse_logical(parsed_expr[2]) + ')'
	elif parsed_expr[0] == 'set': #['set', L_var, logical_expr]
		expr_string = '{' + parsed_expr[1] + ' | ' + unparse_logical(parsed_expr[2]) + '}'
	return expr_string

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
		
# Universal:	['A', ['U', _, _], L_var]
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
		
# Existential: 	['A', ['EI', L_var, expr], ['EE', L_var, expr, expr]]
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

# Equality: ['SUB', expr, prop, ['EQ', expr, expr], equality]				
def check_equality_reduction(parsed_expr):
	if (parsed_expr[0] == 'SUB0' or parsed_expr[0] == 'SUB1') and parsed_expr[3][0] == 'EQ':
		return True
	else:
		return False

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

# ['SUB0', expr, prop, ['EQ', expr, expr], equality]		
def perform_equality_reduction(parsed_expr):
	parsed_prop = parsed_expr[2]
	parsed_equality = parsed_expr[4]
	
	result = []
	# no occurrences of the right hand expr if sub0 or vice versa
	# i.e. the substitution changed nothing
	if (parsed_expr[0] == 'SUB0' and not is_subformula_of(parsed_equality[2], parsed_prop)) or (parsed_expr[0] == 'SUB1' and not is_subformula_of(parsed_equality[1], parsed_prop)):
		result = parsed_expr[1] #return the lambda term for the proposition prior to the vacuous substitution
	# wedge
	elif parsed_prop[0] == 'wedge':
		# "distributes" the substitute action into the conjunction
		sub_left = [parsed_expr[0], ['A', parsed_expr[1], ['Pi0']], parsed_prop[1], parsed_expr[3], parsed_equality]
		sub_right = [parsed_expr[0], ['A', parsed_expr[1], ['Pi1']], parsed_prop[2], parsed_expr[3], parsed_equality]
		result = ['P', sub_left, sub_right]
	# rightarrow
	elif parsed_prop[0] == 'rightarrow':
		# this one sucks...seriously
		opposite = ''
		if parsed_expr[0] == 'SUB0':
			opposite = 'SUB1'
			replaced = parsed_equality[2]
			replacer = parsed_equality[1]
		elif parsed_expr[0] == 'SUB1':
			opposite = 'SUB0'
			replaced = parsed_equality[1]
			replacer = parsed_equality[2]
		# needs a new variable to instantiate the new assumption
		remaining_variables = set(var_list).difference(set(used_variables))
		new_variable = remaining_variables.pop()
		used_variables.append(new_variable)
		inner_sub = [opposite, new_variable, replace_subformula(parsed_prop[1], replaced, replacer), parsed_expr[3], parsed_equality]
		apply = ['A', parsed_expr[1], inner_sub]
		outer_sub = [parsed_expr[0], apply, parsed_prop[2], parsed_expr[3], parsed_equality]
		result = ['L', new_variable, outer_sub]
	# forall
	elif parsed_prop[0] == 'forall':
		uni_variable = parsed_prop[1].strip('l')
		inner = [parsed_expr[0], ['A', parsed_expr[1], uni_variable], parsed_prop[2], parsed_expr[3], parsed_equality]
		result = ['U', uni_variable, inner] 
	elif parsed_prop[0] == 'in':
		# t(x) in {z | B(z, x)}
		if parsed_prop[2][0] == 'set':
			inner = [parsed_expr[0], ['OUT', parsed_expr[1]], replace_subformula(parsed_prop[2][2], parsed_prop[2][1], parsed_prop[1]), parsed_expr[3], parsed_equality]
			result = ['IN', inner]
		# t in x 
			# (x not free in t)
		elif (parsed_expr[0] == 'SUB0' and not is_subformula_of(parsed_equality[2], parsed_prop[1])) and is_subformula_of(parsed_equality[2], parsed_prop[2]):
			instantiate_variable = parsed_prop[1]
			if isinstance(instantiate_variable, str):
				instantiate_variable = instantiate_variable.strip('l')
			result = ['A', parsed_expr[3][2], instantiate_variable]			
		elif (parsed_expr[0] == 'SUB1' and not is_subformula_of(parsed_equality[1], parsed_prop[1])) and is_subformula_of(parsed_equality[1], parsed_prop[2]):
			instantiate_variable = parsed_prop[1]
			if isinstance(instantiate_variable, str):
				instantiate_variable = instantiate_variable.strip('l')
			result = ['A', parsed_expr[3][1], instantiate_variable]
		# t(x) in x 
			# (x free in t)
		elif (parsed_expr[0] == 'SUB0' and is_subformula_of(parsed_equality[2], parsed_prop[1])) and is_subformula_of(parsed_equality[2], parsed_prop[2]):
			inner = ['A', parsed_expr[3][2], parsed_prop[1]]
			new_prop = ['in', parsed_prop[1], parsed_equality[1]]
			result = [parsed_expr[0], inner, new_prop, parsed_expr[3], parsed_equality]	
		elif (parsed_expr[0] == 'SUB1' and is_subformula_of(parsed_equality[1], parsed_prop[1])) and is_subformula_of(parsed_equality[1], parsed_prop[2]):
			inner = ['A', parsed_expr[3][1], parsed_prop[1]]
			new_prop = ['in', parsed_prop[1], parsed_equality[2]]
			result = [parsed_expr[0], inner, new_prop, parsed_expr[3], parsed_equality]
		# t(x) in z
			# nothing to do in the event of this form
			# implicit non-normal
		elif (parsed_expr[0] == 'SUB0' and is_subformula_of(parsed_equality[2], parsed_prop[1])) and not is_subformula_of(parsed_equality[2], parsed_prop[2]):
			print("Implicit cut, no reduction possible.")
		elif (parsed_expr[0] == 'SUB1' and is_subformula_of(parsed_equality[1], parsed_prop[1])) and not is_subformula_of(parsed_equality[1], parsed_prop[2]):
			print("Implicit cut, no reduction possible.")		
	# t(x) = u(x)
	elif parsed_prop[0] == '=':
		opposite = ''
		if parsed_expr[0] == 'SUB0':
			opposite = 'SUB1'
			replaced = parsed_equality[2]
			replacer = parsed_equality[1]
		elif parsed_expr[0] == 'SUB1':
			opposite = 'SUB0'
			replaced = parsed_equality[1]
			replacer = parsed_equality[2]
		remaining_variables = set(var_list).difference(set(used_variables))
		new_variable1 = remaining_variables.pop()
		used_variables.append(new_variable1)	
		inner_left = [opposite, new_variable1, ['in', 'z', replace_subformula(parsed_prop[1], replaced, replacer)], parsed_expr[3], parsed_equality]
		remaining_variables = set(var_list).difference(set(used_variables))
		new_variable2 = remaining_variables.pop()
		used_variables.append(new_variable2)			
		inner_right = [opposite, new_variable2, ['in', 'z', replace_subformula(parsed_prop[2], replaced, replacer)], parsed_expr[3], parsed_equality]
		middle_left = ['SUB1', inner_left, ['in', 'z', parsed_prop[1]], parsed_expr[1], parsed_prop]
		middle_right = ['SUB0', inner_right, ['in', 'z', parsed_prop[2]], parsed_expr[1], parsed_prop]
		outer_left = [parsed_expr[0], middle_left, ['in', 'z', parsed_prop[2]], parsed_expr[3], parsed_equality]
		outer_right = [parsed_expr[0], middle_right, ['in', 'z', parsed_prop[1]], parsed_expr[3], parsed_equality]
		result = ['EQ', ['U', 'z', ['L', new_variable1, outer_left]], ['U', 'z', ['L', new_variable2, outer_right]]]
	# vee
	elif parsed_prop[0] == 'vee':
		remaining_variables = set(var_list).difference(set(used_variables))
		new_variable1 = remaining_variables.pop()
		new_variable2 = remaining_variables.pop()
		used_variables.append(new_variable1)
		used_variables.append(new_variable2)
		inner_left = ['I0', [parsed_expr[0], new_variable1, parsed_prop[1], parsed_expr[3], parsed_equality]]
		inner_right = ['I1', [parsed_expr[0], new_variable2, parsed_prop[2], parsed_expr[3], parsed_equality]]
		middle = ['DE', new_variable1, inner_left, new_variable2, inner_right]
		result = ['A', parsed_expr[1], middle]
	# exists
	elif parsed_prop[0] == 'exists':
		#Existential intro as EI(m, u) 			['EI', L_var, expr]		
		#Existential elim as EE((x,s).v)		['EE', L_var, var(?), expr]
		remaining_variables = set(var_list).difference(set(used_variables))
		new_variable = remaining_variables.pop()
		used_variables.append(new_variable)
		inner = [parsed_expr[0], new_variable, parsed_prop[2], parsed_expr[3], parsed_equality]
		middle = ['EE', parsed_prop[1], new_variable, inner]
		result = ['A', parsed_expr[1], middle]
	return result
			
# Traverse the parsed expression and find a reduction
# Can't guarantee much about what order this algorithm proceeds, 
# but it will find all reductions
# Could use serious refactoring: return result moved out of the if statements
#								 put each reduction in its own function
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
		#Existential: 	['A', ['EI', L_var, expr], ['EE', L_var, var, expr]]
		#first_var = parsed_expr[2][1]
		#primary_expr = parsed_expr[2][3]
		#first_secondary_expr = parsed_expr[1][1]
		#second_var = parsed_expr[2][2]
		#second_secondary_expr = parsed_expr[1][2]
		#result = substitute(first_var, primary_expr, first_secondary_expr)
		#result = substitute(second_var, result, second_secondary_expr)
		var = parsed_expr[2][2]
		primary_expr = parsed_expr[2][3]
		secondary_expr = parsed_expr[1][2]
		result = substitute(var, primary_expr, secondary_expr)
		return result
	elif check_membership_reduction(parsed_expr):
		#Membership: 	['OUT', ['IN', expr]]
		result = parsed_expr[1][1]
		return result
	elif check_universal_reduction(parsed_expr):
		#Universal: 		['A', ['U', _, _], L_var]
		#var = parsed_expr[1][1]
		#primary_expr = parsed_expr[1][2]
		#secondary_expr = parsed_expr[2]
		#result = substitute(var, primary_expr, secondary_expr)		
		result = parsed_expr[1][2]
		return result
	elif check_equality_reduction(parsed_expr): 
		#Equality: ['SUB', expr, prop, ['EQ', expr, expr], equality]
		result = perform_equality_reduction(parsed_expr)
		return result
	else: 
		if parsed_expr[0] == 'A':
			result = ['A', find_reduction(parsed_expr[1]), find_reduction(parsed_expr[2])]
			return result
		elif parsed_expr[0] == 'L':
			result = ['L', parsed_expr[1], find_reduction(parsed_expr[2])]
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
		elif parsed_expr[0] == 'EQ':
			result = ['EQ', find_reduction(parsed_expr[1]), find_reduction(parsed_expr[2])]
			return result
		elif parsed_expr[0] == 'SUB0' or parsed_expr[0] == 'SUB1':
			result = [parsed_expr[0], find_reduction(parsed_expr[1]), parsed_expr[2], find_reduction(parsed_expr[3]), parsed_expr[4]]
			return result
		else:
			return parsed_expr
			
def normalize(parsed_expr, max_iterations = 10):
	iterations = 1
	pre_reduced = parsed_expr
	reduced = find_reduction(parsed_expr)
	print("Iteration:", iterations, "\n current expression:", reduced)
	while iterations < max_iterations and pre_reduced != reduced:
		pre_reduced = reduced
		reduced = find_reduction(reduced)
		iterations += 1
		print("Iteration:", iterations, "\n current parsed expression:", reduced, "\n unparsed expression: ", unparse(reduced))
	return reduced
	
# This is definitely not the most efficient program possible due to re-scanning and many many other redundancies.

# Test code
if __name__ == "__main__":

	def run_test(test_string):
		test_parse = expr.parseString(test_string)
		print(test_parse)
		#print("Unparsed: ", unparse(test_parse), "Original: ", test_string, unparse(test_parse) == test_string)
		if unparse(test_parse[0].asList()) == test_string:
			print("Unparsed parsed matches original.")
		else: 
			print("Unparse:", unparse(test_parse[0].asList()))
		normalize_result = normalize(test_parse[0].asList())
		print("Normal:", unparse(normalize_result))
		print()
		
	def run_logical_test(logical_test_string):
		logical_test_parse = logical_expr.parseString(logical_test_string)
		print(logical_test_parse)
		if (not isinstance(logical_test_parse[0], str)) and unparse_logical(logical_test_parse[0].asList()) == logical_test_string:
			print("Unparsed parsed matches original.")
		else: 
			print("Unparse:", unparse_logical(logical_test_parse[0]))
		print()
	
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
	print()
	
	test_string = '(Lx.(OUT(x)x))'
	run_test(test_string)

	test_string = 'IN(x)'
	run_test(test_string)
	
	test_string = 'IN((Lx.(OUT(x)x)))'
	run_test(test_string)
	
	test_string = '((Lx.(OUT(x)x))IN((Lx.(OUT(x)x))))'
	test_parse = expr.parseString(test_string)
	print(test_parse)
	normalize_result = normalize(test_parse[0].asList(), max_iterations = 5)
	print()
	

	# parse_proof_1 = expr.parseString(proof_1)
	# print(parse_proof_1)
	# if unparse(parse_proof_1[0].asList()) == proof_1:
		# print("Unparsed parsed matches original.")
	# else: 
		# print("Unparse:", unparse(parse_proof_1))
	# print()
	
	# Proof that {t, t} = {t}
	proof_1 = 'EQ((La.IN(I0(OUT(a)))), (Lb.(OUT(b)DE(c.IN(c), d.IN(d)))))'	
	run_test(proof_1)

	run_logical_test('lx')
	run_logical_test('(la vee la)')
	run_logical_test('(lx = lx)')	
	run_logical_test('(lx = lt)')	
	run_logical_test('{lx | (lx = lt)}')
	run_logical_test('({lx | (lx = lt)} in {lx | ((lx = {ly | (ly = lt)}) vee (lx = {ly | ((ly = lt) vee (ly = lt))}))})')
	
	# Proof that {{t}} = <t, t>
	proof_2 = 'EQ((La.SUB0(IN(I0(EQ((Lb.b), (Lc.c)))) :\
				( {lx | (lx = lt)} in {lx | ((lx = {ly | (ly = lt)}) vee (lx = {ly | ((ly = lt) vee (ly = lt))}))} ), \
				OUT(a) : ( lx = {lx | (lx = lt)} ) ) ), \
				(Ld.(OUT(d)DE(e.IN(e), f.IN(SUB0(f :\
				( lx = {lx | ((lx = lt) vee (lx = lt)) } ), ' + \
				proof_1 + \
				': ( {lx | (lx = lt) } = {lx | ((lx = lt) vee (lx = lt)) } ) ) ) ) ) ) )'
	print(proof_2)
	run_test(proof_2)
	
	#Does white space matter?
		#white space ignored by default in pyparser
	
	#Lambda: 		['A', ['L', _, _], expr]
	#Universal: 	['A', ['U', _, _], L_var]
	#Conjunction:	['A', ['P', _, _], ['Pi0']]
	#Disjunction: 	['A', ['I0', expr], ['DE', var, expr, var, expr]]
	#Existential: 	['A', ['EI', L_var, expr], ['EE', L_var, expr, expr]]
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
