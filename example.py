
def f(x): 

	requires(x < 2)
	x = 1 # x1
	if x == 1:
		x +=2 # x2
		if x == 2:
			x += 3 # x3
		# x4 = (x2 or x3) 
		x += 5 # x5
		# x6 = (x1 or x5)
	elif x == 6:
		x = 7
		# x8 = (x6 or x7)
	else:
		x = 9
	# x10 = (x8 or x9)
	x += 11

	assures(x > 0)
