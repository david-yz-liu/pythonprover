
def f(x): 
	requires(x == 1)
	while x <= 5:
		x += 1
	assures(x == 5)
