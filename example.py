def g(x):
	x += 1
	return x

def f(x): 
	requires(x == 0)

	x = g(x)

	assures(x == 2) #should fail
