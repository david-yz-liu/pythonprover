# requires(f(x, y) > 0)
def f(x, y):
	requires(x > 4)
	assures(x > 0)
	x = x - 5
	return x

