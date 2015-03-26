
def f(x): 
	requires(x == 1)
	for i in range(0, 5, 2):
		x = i
	assures(x == 4)

