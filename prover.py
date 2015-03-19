import ast
import astpp
import sys
from ast import *
import imp
import re
from pprint import pprint
from operator import itemgetter
import copy
# import z3
# from z3 import *
# import codegen 
# from codegen import *

# Codegen
codegen = imp.load_source('codegen', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/codegen/codegen.py')

# Z3
# sys.path.append('/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/')
sys.path.append('/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/')
z3 = imp.load_source('z3.py', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/z3.py')

global_solver = z3.Solver()
global_vars = {}

# Since print(<z3.Solver()>) doesn't work, use this list to debug/keep track of what's in the solver
z3_calls = []
z3_vars = []


# TODO:
# variable instantiation 
#     - declare new incremented variable
#     - assert its relationship to the old one
# if statements
#     - condition implies new var == final var at end of body
#     - new var = Or (final var at end of if, final var at end of else)
#     - NEED: final vars for each
#             before var
#             after var

def pretty_print_dic(dictionary):
    # exec("print('"+str(dictionary)+"'')") # Print name of dictionary
    for k, v in sorted(dictionary.items(), key=itemgetter(1)):
        print (k, ":", v)

''' return the ast.Return node of the given ast.FunctionDef node, if there is one'''
def get_return(node):
    if not isinstance(node, FunctionDef):
        raise TypeError('expected FunctionDef, got %r' % node.__class__.__name__)
    
    for sub_elem in node.body:
        if isinstance(sub_elem, ast.Return):
            return sub_elem.value

''' Return a the list of parameters reuired by the given function'''
def get_func_args(node):
    if not isinstance(node, FunctionDef):
        raise TypeError('expected FunctionDef, got %r' % node.__class__.__name__)
    
    args = []
    arg_list = node.args.args
    
    for elem in arg_list:
        args.append(elem.arg)

    return args

''' The main thing '''
class Z3Visitor(ast.NodeVisitor):

    def visit_For(self, node):
        pass
    
    def visit_While(self, node):
        pass

    def visit_If(self, node):

        # rebuild the condition with variable substitution from local_vars
        # condition = codegen.to_source(node.test)
        # for key in global_vars:
        #     condition = re.sub(key, global_vars[key], condition)


        # Take a snapshot of the variable set before entering the if-elif-else block
        before = copy.copy(global_vars)
        
        # Create a visitor to visit the if-elif-else block
        if_visitor = Z3Visitor()
        # Visit body
        for elem in node.body:
            if_visitor.visit(elem)

        # Take a snapshot of the variable set after exiting the if-elif-else block
        after = copy.copy(global_vars)
        print("before", before)
        print("after", after)
        # Check which variables have changed, create new incremented variables that
        # are either the old or the new value. This represents the if-elif-else block
        for key in after:
            if before[key] != after[key]:
                cur_var = after[key]
                incremented = cur_var[:1] + str(eval(cur_var[1:]+ "+ 1"))
                global_vars[incremented] = "OR("+before[key]+", "+after[key]+")"
                print("OR("+before[key]+", "+after[key]+")")

        # # Loop over elifs (if any) until we find a satisfiable one.
        # cur_orelse = node.orelse
        # while len(cur_orelse) == 1 and isinstance(cur_orelse[0], ast.If): # i.e. another elif. other possibilities: [] == no else statement, [NodeA, nodeB, ...] == else body
        #     print("**********\ncur_orelse", cur_orelse)
        #     # Having to index into a list like this is terrible, clean up later
        #     # Build the test condition, substitute any variables
        #     condition = codegen.to_source(cur_orelse[0].test)
        #     for key in self.which:
        #         condition = re.sub(key, self.local_vars[self.which[key]], condition)

        #     # Create solver, check condition, execute body if condition is true - same as above with If
        #     elif_visitor = Z3Visitor(copy.copy(self.local_vars), copy.copy(self.which), copy.copy(self.assertions))
        #     so_far = z3.Solver()
        #     eval("so_far.add"+condition)
        #     for assertion in self.assertions:
        #         eval("so_far.add("+assertion+")")

        #     if str(so_far.check()) == 'sat':

        #         print("visiting elif-body")
        #         # Visit body
        #         for elem in cur_orelse[0].body:
        #             elif_visitor.visit(elem)

        #     # Iterate
        #     cur_orelse = cur_orelse[0].orelse

        # # Deal with the else statement (possibly empty)
        # else_visitor = Z3Visitor(copy.copy(self.local_vars), copy.copy(self.which), copy.copy(self.assertions))

        # for elem in cur_orelse:
        #     else_visitor.visit(elem)



    def visit_IfExpr(self, node):
        pass
        # An expression such as a if b else c

    def visit_Expr(self, node):
        # check for 'requires(...)' and 'assures(...)''
        # can probably optimize this function by merging both cases
        if isinstance(node.value, ast.Call) and \
            isinstance(node.value.func, ast.Name):
            if node.value.func.id == 'requires':
                # Uncompile 'bodyx' in 'requires(body1, body2, ...) for all x
                for condition in node.value.args:
                    body = codegen.to_source(condition)
                    # self.assertions.append(body)
                    # eval("self.solver.add"+body)
                    print ("s.add"+body)

            elif node.value.func.id == 'assures':
                # Uncompile 'bodyx' in 'assures(body1, body2, ...) for all x
                for condition in node.value.args:
                    body = codegen.to_source(condition)

                    # Substitute variables in body with the corresponding value
                    # found in the global variable dictionary
                    for key in global_vars:
                        body = re.sub(key, global_vars[key], body)

                    # eval("self.solver.add"+body)
                    # self.assertions.append(body)
                    print ("s.add"+body)
        else:
            print ("Expr:", codegen.to_source(node))

    ''' Update/Add to the local_vars dictionary to reflect the latest assignment'''
    def visit_Assign(self, node):
        LHS = node.targets[0] # left hand side (Name or Tuple obj)
        RHS = node.value # right hand side

        # Create a list of targets to assign to
        targets = []
        if isinstance(LHS, ast.Tuple): # multiple, comma seperated, targets
            for target in LHS.elts:
                targets.append(target.id)
        else: # assignment of form: x1 = x2 = ... = <RHS> for all xn where 0 < n
            for nameObj in node.targets: 
                targets.append(nameObj.id)  

        # assemble the right hand side of the assignment
        body = codegen.to_source(RHS)
        for key in global_vars:
            # substitute any variables with their present incremented variable
            body = re.sub(key, global_vars[key], body)

        for target in targets:
            if target not in global_vars: # New variable
                global_vars[target] = target
                exec("global "+target)
                exec(target+" = z3.Int('"+target+"')", globals())
                exec("global_solver.add("+target+" == "+body+")")
                z3_vars.append(target)
                z3_calls.append(target+" == "+body)

            else: # Existing variable
                cur_var = global_vars[target]
                # create a new incremented variable based off of 'target'
                incremented = cur_var[:1] + str(eval(cur_var[1:]+ "+ 1"))
                # Update variable dictionary
                global_vars[target] = incremented
                # Declare incremented as z3 object
                exec("global "+incremented)
                exec(incremented+" = z3.Int('"+incremented+"')", globals())
                # Declare the new variable's relationship with its predecessor
                exec("global_solver.add("+incremented+" == "+body+")")

                z3_vars.append(incremented)
                z3_calls.append(incremented+" == "+body)


    ''' Will be used to check for calls to functions we have instantiated z3
        equivalents to, and call those equivalents with the given arguments'''

    def visit_AugAssign(self, node):
        target = node.target.id
        cur_var = global_vars[node.target.id] # The current incremented variable representing target

        RHS = codegen.to_source(node.value)
        # Rebuild RHS: Substitute the dictionary value of each variable
        for key in global_vars:
            # substitute any variables with their present values
            RHS = re.sub(key, global_vars[key], RHS)

        if isinstance(node.op, ast.Add):
            operator = '+'
        elif isinstance(node.op, ast.Sub):
            operator = '-'
        elif isinstance(node.op, ast.Mult):
            operator = '*'
        elif isinstance(node.op, ast.Div):
            operator = '/'
        elif isinstance(node.op, ast.Mod):
            operator = '%'
        else:
            print("Augmented Assignment of type", node.op.op, "not yet implemented")
            return

        # Build the new variable's relationship with its predecessor
        body = cur_var+" "+operator+" "+RHS

        # Create a new incremented variable based off of 'target'
        incremented = cur_var[:1] + str(eval(cur_var[1:]+ "+ 1"))
        # Update the variable dictionary
        global_vars[target] = incremented
        # Declare incremented as z3 object
        exec("global "+incremented)
        exec(incremented+" = z3.Int('"+incremented+"')", globals())
        # Declare the new variable's relationship with its predecessor
        exec("global_solver.add("+incremented+" == "+body+")")

        z3_vars.append(incremented)
        z3_calls.append(incremented+" == "+body)

    def visit_Call(self, node):
        pass
        # print ("Call:", codegen.to_source(node))

    def visit_FunctionDef(self, node):
        
        # print ("Func:", codegen.to_source(node)) # This blows up for some reason

        arg_list = get_func_args(node)

        for arg in arg_list:
            # Declare each parameter as a global variable
            if arg not in global_vars: # New variable
                global_vars[arg] = arg
                exec("global "+arg)
                exec(arg+" = z3.Int('"+arg+"')", globals())
                z3_vars.append(arg)

        # Visit function body and build z3 representation
        func_visitor = Z3Visitor()
        for elem in node.body:
            func_visitor.visit(elem)

    def visit_Return(self, node):
        print ("Return:", codegen.to_source(node))


with open (sys.argv[1], "r") as myfile:
        data = myfile.read()


tree = ast.parse(data)
print ("------- original -------")
print (astpp.dump(tree))

# Visit AST and aggregate Z3 function calls
my_visitor = Z3Visitor()
my_visitor.visit(tree)

result = global_solver.check()
print ("RESULT:", result)
print ("vars")
print(global_vars)
print ("\nvars", len(z3_vars))
for var in sorted(z3_vars):
    print(var)
print ("\ncalls", len(z3_calls))
for call in sorted(z3_calls):
    print (call)

# print(global_solver)
# print(global_solver.model())

# if (result):
#     m = s.model()
#     print("Model: ", m)

# Testing validity: Requires building a function of the form:
'''
def prove(f):
s = Solver()
s.add(Not(f))
if s.check() == unsat:
print "proved"
else:
print "failed to prove"
'''

'''
////////////////////////////// RULES /////////////////////////////////
1. In the users code, Pre-conditions must be declared after the function
definition line 'def f(x):', because the z3 variables referenced in the 
pre/post condition calls are instantiated when the function def line is parsed. 

2. Post conditions must be declared after the function body, because we must first
read through the body to see how variables are modified. 

////////////////////////////// NOTES /////////////////////////////////
1. Variables and their values are added to the local dictionary:
    - upon any assignment
    - upon reading the arguments of a FunctionDef

//////////////////////////// WARNINGS ///////////////////////////////
codegen.to_source does return nothing when reading 'True' or 'False'
and will not fill in function def paramenters codegen.to_source('f(x,y)') == f( , )

'''