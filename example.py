# requires(f(x, y) > 0)
def f(x, y, j): 

	requires(x == 5)

	x = x - 10 # multiple modifications in a row (checking the correct creation of new xn vars)
	x = x / 2

	a = 3.14 # declaration of new variable
	k = 2
	b = x + y # Assignment from other variables
	x, y, z, t = 14 # Multiple assignments on one line
	# a = b = 111 # Multiple assignment

	# # Augmented assignments
	x += 5 # Num object
	t *= x # Name object
	t -= (a+b) # with BinOp object
	x = 11 # TODO simple assignments at end
	t %= 3 #  Modulus
	t += j #  Referencing variable with an unknown value

	return x

	assures(x > 0)

# z = Int('z')
# s = Solver()
# ...
# s.add(mydict['z3'] > 5)
# s.solve()
# 'sat'

# x1 : ((x) + 4+4)

# x2 : ((x) + 4) + 5
# x1 : (x) + 4
# x2 : (((x) + 4) + 5)
# x1 : (x) + 4