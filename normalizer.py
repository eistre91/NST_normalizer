"""
	Will attempt to normalize given lambda terms for NNST. 
	
	Syntax:
		Lambdas are to be written as L
		Universal Quantification as U
		Pairing as < _, _ >
		Pi_i as P
		Iota as I0(u) or I1(i)
		Existential introduction as (m, u)
		Existential elimination as [(x,s).v]
		Membership as out(u) and in(u)
		Equality introduction as eq(_ ,_)
		Substitution as sub(_, _)
		
	Outer parenthesis are not needed. 
	All other parenthesis can not be omitted.
"""
import re

def escape_string(s):
	return s.translate(str.maketrans({'(': r'\(', \
									')': r'\)', \
									'.': r'\.'}))							

# Pass in an expression with the bound variable to be replaced
# Accepts the expression without the corresponding binding (i.e. without the lambda)
def variable_substitute(variable, primary_exp, secondary_exp):
	print("VS Test code:",re.sub(variable, secondary_exp.strip('()'), primary_exp))
	return re.sub(variable, secondary_exp.strip('()'), primary_exp)
	
def substitute(replaced_exp_pat, primary_exp, secondary_exp):
	print("S Test code:",replaced_exp_pat, secondary_exp, primary_exp)
	print(re.sub(replaced_exp_pat, secondary_exp, primary_exp))
	return re.sub(replaced_exp_pat, secondary_exp, primary_exp)

# Applies a single step of the reduction process to an expression.
# Optionally accepts a particular reduction to perform
# Otherwise it looks for one to perform by precedence of reductions
# in a leftmost greedy wise fashion as per the default operation of regular expressions.
# Returns the reduced expression or None if no reduction found.
def step_reduce(expression, which = None):
	reduced_exp = None
	result = None
	if which == None:
		lambda_reduction = re.search(r'\(L([a-z])\.(.+)\)(\(.+?\))', expression)
		if lambda_reduction != None:
			replaced_exp = lambda_reduction.group(0)
			variable = lambda_reduction.group(1)
			primary_exp = lambda_reduction.group(2)
			secondary_exp = lambda_reduction.group(3)
			print("Applying lambda reduction for", expression, "at", replaced_exp)
			reduced_exp = variable_substitute(variable, primary_exp, secondary_exp)
			replaced_exp_pat = escape_string(replaced_exp)
			result = substitute(replaced_exp_pat, expression, reduced_exp)
		else:
			print("No reduction found.")
	else:
		pass
		
	return result

# Will apply reductions step by step and stop after it finds no reductions
# Or until it reaches the maximum iterations
def normalize(expression, max_iterations = 100):
	stored_expression = expression
	current_expression = step_reduce(expression)
	iterations = 1
	print("At iteration", iterations, "expression is", current_expression)
	while iterations <= max_iterations and current_expression != None:
		stored_expression = current_expression
		iterations += 1
		current_expression = step_reduce(current_expression)
		print("At iteration", iterations, "expression is", current_expression)
	return stored_expression

# Test code
if __name__ == "__main__":
	assert step_reduce('(Lx.(x))(y)') == '(y)'
	assert normalize('(Lx.(x))(y)') == '(y)'
	
	assert step_reduce('Lz.((Lx.(x))(y))') == 'Lz.((y))'
	assert normalize('Lz.((Lx.(x))(y))') == 'Lz.((y))'
	
	assert normalize('Lz.((Lx.(x)(x))(y))') == 'Lz.((y)(y))'
	assert normalize('(Lx.((x)(x)))(y)') == '(y)(y)'
	
	assert normalize('Lz.((z))') == 'Lz.((z))'
	assert normalize('(Lz.((z)))') == '(Lz.((z)))'
	
	assert normalize('(x)(y)(z)') == '(x)(y)(z)'
	assert normalize('(Lx.(y))(z)') == '(y)'
	assert normalize('(Lx.(x))(Ly.(y))') == 'Ly.(y)'
	assert normalize('(Lz.((Lx.(x)(x))(z)))(t)') == '(t)(t)'
	
#History of errors 
	# The match is greedily grabbing (y)) rather than (y)
	# assert step_reduce('Lz.((Lx.(x))(y))') == 'Lz.(y)'
	# Status: Fixed
	
	# Performing substitution but then not substituting the reduced expression
	# back in to the original
	# assert step_reduce('Lz.((Lx.(x))(y))') == 'Lz.(y)'
	# Status: Broken