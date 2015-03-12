# requires(f(x, y) > 0)
def f(x, y): 

	requires(x == 5)

	x = x - 10 # multiple modifications in a row (checking the correct creation of new xn vars)
	x = x / 2
	x, y = 14 # Multiple assignments on one line
	a = 1 # declaration of new variable
	b = x + y # Assignment from other variables
	# # a = b = 1 # Multiple assignment

	# # Augmented assignments
	# x += 4 # Num object
	# t *= x # Name object
	# t -= (k+t) # with BinOp object
	# # x = 11 # TODO simple assignments at end
	# # t %= 3 # TODO - Modulus
	# # t += j # TODO - Referencing variable with an unknown value
	# # def t1 where t1 = t + j
	return x

	assures(x > 0)

# z = Int('z')
# s = Solver()
# ...
# s.add(mydict['z3'] > 5)
# s.solve()
# 'sat'