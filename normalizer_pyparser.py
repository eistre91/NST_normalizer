from pyparsing import *

"""
	Will attempt to normalize given lambda terms for NNST. 
	
	Syntax:
		Lambdas are to be written as L    		['L', variable, expr]
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
		lparens + Group( lam('rule') + var('variable') + dot.suppress() + expr('expr')) + rparens
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
	
# Couldn't figure out how to make results names work.