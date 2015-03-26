
def f(x): 
	requires(x == 1)
	for i in range(4):
		x += i
	assures(x == 7)


