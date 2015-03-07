# requires(f(x, y) > 0)
def f(x, y):
	requires(x == 5, y > 0)
	x = x - 3 # modification of existing var
	t, y = -1 # multiple assignments on one line (and declaration of new var)
	assures(x > 0, y == -1)
	return x

