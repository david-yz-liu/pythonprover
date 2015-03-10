# requires(f(x, y) > 0)
def f(x): 

	requires(x == 5)

	x = x - 10
	# x = x - 3 # Modification of existing variable
	# t, y = -1 # Multiple assignments on one line and declaration of new variable
	# k = x + t # Assignment from other variable
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