
def odd_or_negative(x, y):
	"""
	Case 1: x is odd. Return 0
	Case 2: x is negative or zero. Return 1
	Otherwise: Return x
	"""
	if x%2 == 1:
		y = 0
	elif x <= 0:
		y = 1
	else:
		y = x
	return y
	#@ assures (y > 0)

def sum_odd_under_ten():
	x = 0
	for i in range(1, 10, 2):
		x += i
	return x
