
def f(x): 

	requires(x < 2)
	x += 1
	if x == 3:
		x = 2
	elif x == 4:
		x = 4
	else:
		x = 6
	x += 8
	# x = x - 10 # multiple modifications in a row (checking the correct creation of new xn vars)	# x = x / 2

	# pie = 3.14 # declaration of new variable
	# b = x + y # Assignment from other variables
	# x, y, z, t = 14 # Multiple assignments on one line
	# a = b = 111 # Multiple assignment
	# t = 1
	# # Augmented assignments
	# x += 5 # Num object
	# t *= x # Name object
	# t -= (y + j) # with BinOp object
	# x = 11 # TODO simple assignments at end
	# t %= 3 #  Modulus
	# t += j #  Referencing variable with an unknown value

	# 	return x

	assures(x > 0)
