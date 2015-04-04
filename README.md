#Python Prover
***

## What is it?

This program supports an extension of Python in which additions to the syntax allow programmers to verify arithmetic functions within their programs for correctness. You will be able to declare pre-conditions, post-conditions, and assertion statements to specify the range of behaviour of your functions. This program is run at compile time, creating a logical representation of your program to determine its satisfiability. Guards against bad user input are still up to you, but this will help keep **you** sane!

Here is a simple example: 

    def gcd(a, b):
      """ Find the Greatest Common Divisor of a and b. """
      #@ requires(a >= b, b > 0)
      while b:
          a, b = b, a%b
      return a
      #@ assures(a > 0)

We have constrained gcd() to operate solely on positive numbers and guarded against division by zero with the *requires* statement (the pre-condition). Additionally, we've provided a little sanity check with the *assures* statement (the post-condition).

If-statements are supported, allowing you to track all possible behaviours of your functions.

    def odd_or_negative(x):
    	"""
    	Case 1: x is odd. Return 0
    	Case 2: x is negative or zero. Return 1
    	Otherwise: Return x
    	"""
    	if x%2 = 1:
    		y = 0
    	elif x <= 0:
    		y = 1
    	else:
    		y = x
    	return y
    	#@ assures (y > 0)

Range based loops: `for i in range (1, 9, 2)` and if-expressions: `x = 1 if y%2 == 1 else 0` are also supported.

This program is a work in progress. I'm currently working on supporting function calls, while-loops, and for-loops that iterate over objects. Eventually I hope to extend support beyond just arithmetics, including string, list and dictionary operations.
***

## Satisfiability and Validity

This program checks for both satisfiability and validity. Depending on your purposes, testing satisfiability may be enough information to debug your code. But sometimes we want the behaviour of a function precisely defined. To achieve validity the post condition must match all possible values of any variable referenced in it. For example:

    def increment(x):
    	#@ requires(x > 0, x < 3)
    	#@ assures(y == 3) 
    	x += 1
    	y = x
    	return y
    	
This function takes 1 or 2 as an argument and returns 2 or 3, respectively. However, since the post condition is does not capture all possible output, this function is invalid. To achieve validity we must be very specific with our post-conditions

## How Does it Work?

This program makes use of the [Python Abstract Syntax Tree](https://docs.python.org/3.4/library/ast.html) (AST) and uses [Z3](http://z3.codeplex.com/) - a Theorem Prover to create a logical formulation of the source code. The source is first compiled into an AST, then a modified AST Visitor traverses the first level of the tree, declaring function prototypes/stubs for each function. Another Visitor then traverses the tree, this time in its entirety, tracking source variables and adding logical assertions about said variables to a Z3 Solver object which is, finally, checked for satisfiability. 

The key idea of the program is that each variable is, when modified, tracked with an incremented version of itself that is defined by its relationship with the most recent version of itself. Let's expand on this nonsense. If we have a function:

    def just_subtract_one(x)
    	x -= 1
    	return x

Then the modification and return of x is represented by:

    x1 = (x - 1)
    return x1

Say we wanted to assure that just_subtract_one always returned a positive integer. We could assure that upon return `x > 0`

    def just_add_one(x)
    	x -= 1
    	return x
    	#@ assures(x > 0)

This would be represented with the assertion that `x1 > 0`

We could achieve the same thing by adding a pre-condition that upon input `x > 2`

    def just_add_one(x)
    	#@ requires (x > 2)
    	x -= 1
    	return x

Since upon input x is unmodified, the requires call would be represented by the assertion that `x > 2`


###If-statements
If a variable could take on multiple values, depending on some condition, we need a way of tracking that too! And so, upon parsing an if block we create a new incremented version of the variable (as usual), but this time we set it to be equal to either itself before Or after the if statement. For instance:

    def double_evens(x):
    	if (x % 2) == 0:
    		x = (x * x)
    	return x

In this case x is represented by:

    x1 = (x * x)
    x2 = Or(x, x1)
    return x2

The same logic is applied with if-elif-else blocks:

    def plus_minus_zero(x):
    	if x > 0:
    		x = 1
    	elif x < 0:
    		x = 2
    	else: 
    		x = 3
    	return x

Would look like this

    x1 = 1
    x2 = Or(x, x1)
    x3 = 2
    x4 = Or(x2, x3)
    x5 = 3
    x6 = (x4, x5)
    return x6 

x6 thus contains all possible values for x

The same logic is used to handle on-liner if-expressions

Of course, our solver has to check satisfiability for each possibility, which can be a quick death to our running time. So when we do know (or at least might know) the result of the condition before run time, we cut out options by adding implication statements. For `plus_minus_zero()` we also have the calls:

    Implies (x > 0, x6 == x1) 
    Implies (x3 < 0, x6 == x4)

This ensures that if, at this point in the program, the sign of x is known, then we do not try to evaluate the program with a variable set we know will never occur.


###For-Loops

The implementation of for-loops at this point is quite simple: we create an equivalent for loop and recurively call our Visitor on the body of the source body for each iteration. Each time the Visitor is called on the body the it simulates the execution of the source's loop body using the logical assertions and variable tracking we have been discussing so far

    def sum_odd_under_ten():
    	result = 0
    	for i  in range(1, 10, 2):
    		result += i
    	return result
    	#@ assure(result == 25)

Would be handled by something like this

    loop_body = get_body()
    *args = get_args()
    for i in range(*args):
    	my_visitor.visit(loop_body)

Which would result in the following assersions:

    x == 0
    i1 == 1
    x1 == x + i1
    i2 == 3
    x2 == x1 + i2
    i3 == 5
    x3 == x2 + i3
    i4 == 7
    x4 == x3 + i4
    i5 == 9
    x5 == x4 + i5
    x5 == 25

## Running it
Usage: python prover.py [-adz] [--astinfo] [--doc] [--z3info] source_file
* Language: python 3.4
* Dependencies: [codegen](https://pypi.python.org/pypi/codegen/1.0), [Z3](http://z3.codeplex.com/)
* Commandline options:
    
        -a or --astinfo (a pretty printout of source_file's abstract syntax tree)
        -d or --doc     (diplay prover.py's doc)
        -z or --z3info  (a print out of z3 variables and assertions)
