
'''
/////////////////////////////////// RULES //////////////////////////////////////
1. In the users code, Pre-conditions must be declared after the function
definition line 'def f(x):', because the z3 variables referenced in the 
pre/post condition calls are instantiated when the function def line is parsed. 

2. Post conditions must be declared after the function body, because we must first
read through the body to see how variables are modified. 

/////////////////////////////////// NOTES //////////////////////////////////////
1. Variables and their values are added to the local dictionary:
    - upon any assignment
    - upon reading the parameters of a FunctionDef Node

////////////////////////////////// WARNINGS ////////////////////////////////////
codegen.to_source doesn't not always acurately return the correct sourec
for the ast node it's called on. It returns nothing when reading 'True' or 'False'
and will not fill in function def paramenters codegen.to_source('f(x,y)') == f( , )

//////////////////////////////////// TODO //////////////////////////////////////
if statements
    - condition implies new var == final var at end of body
    - new var = Or (final var at end of if, final var at end of else)
Find a way out of hard indexing into orelse nodes in an ast.if Node
'''

import ast
from ast import *
import astpp
import sys
import imp
import re
import copy
from pprint import pprint
from operator import itemgetter

# Codegen
codegen = imp.load_source('codegen', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/codegen/codegen.py')
# Z3
sys.path.append('/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/')
z3 = imp.load_source('z3.py', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/z3.py')

# The solver in which all z3 assertions go
global_solver = z3.Solver()
# Dictionary that keeps track of the current version of a variable
# e.g. {x : x, y : y3}
global_vars = {}

# Since print(<z3.Solver()>) doesn't work, use these lists to
# debug/keep track of what's in the solver
z3_calls = []
z3_vars = []

def pretty_print_dic(dictionary):
    """
    Print a dictionary out in a readable format
    """
    for k, v in sorted(dictionary.items(), key=itemgetter(1)):
        print (k, ":", v)

def get_return(node):
    """
    Return the AST Return Node of the given AST FunctionDef Node, if there is one
    """
    if not isinstance(node, FunctionDef):
        raise TypeError('expected FunctionDef, got %r' % node.__class__.__name__)
    
    for sub_elem in node.body:
        if isinstance(sub_elem, ast.Return):
            return sub_elem.value

def get_func_args(node):
    """
    Return a the list of parameters taken by the given AST functionDef Node
    """
    if not isinstance(node, FunctionDef):
        raise TypeError('expected FunctionDef, got %r' % node.__class__.__name__)
    
    args = []
    arg_list = node.args.args
    
    for elem in arg_list:
        args.append(elem.arg)

    return args

def calculate_conditional_vars(before, after):
    """ 
    Determine which variables are changed by a if-elif-else block
    and create new incremented variables that evaluates to either 
    the original value, or the value produced by the if-elif-else block. 
    These new variables effectively represent the if-elif-else block
    """
    for key in after:
        if before[key] != after[key]:
            cur_var = after[key]
            # create a new incremented variable based off of 'target'
            incremented = cur_var[:1] + str(eval(cur_var[1:]+ "+ 1"))
            # Update variable dictionary
            global_vars[key] = incremented
            # Declare new z3 variable
            exec("global "+incremented)
            exec(incremented+" = z3.Int('"+incremented+"')", globals())
            # Give it the two possible values
            exec("global_solver.add(z3.Or("+incremented+" == "+before[key]+", "+incremented+" == "+after[key]+"))")

            # Track new vars and assertions for debugging purposes
            z3_vars.append(incremented)
            z3_calls.append("Or("+incremented+" == "+before[key]+", "+incremented+" == "+after[key]+")")

class Z3Visitor(ast.NodeVisitor):
    """
    The main thing! Reads over an AST and determines if the program the AST 
    represents is satisfiable.
    """

    def visit_For(self, node):
        pass
    
    def visit_While(self, node):
        pass

    def visit_If(self, node):
        """
        Visit an if-elif-else block. For each condition, create a Z3Visitor 
        to visit said condition's body (and recurse into any nested 
        if-conditions/loops etc. if necessary)
        """
        # Key: condition
        # Value: State of global vars (at this point in execution) if condition satisfied
        after_var_sets = {}

        # If:
        # rebuild the condition with variable substitution from local_vars
        condition = codegen.to_source(node.test)
        for key in global_vars:
            condition = re.sub(key, global_vars[key], condition)

        # Take a snapshot of the variable set before entering the if-elif-else block
        before = copy.copy(global_vars) # snapshot
        
        # Create a visitor to visit the if-elif-else block
        if_visitor = Z3Visitor()
        # Visit body
        for elem in node.body:
            if_visitor.visit(elem)

        # Take a snapshot of the variable set after exiting the if-elif-else block
        after = copy.copy(global_vars) # snapshot 
        
        calculate_conditional_vars(before, after)

        after_var_sets[condition] = after

        # Elifs:
        # Loop over elifs (if any) until we find a satisfiable one.
        cur_orelse = node.orelse
        while len(cur_orelse) == 1 and isinstance(cur_orelse[0], ast.If): # i.e. another elif. other possibilities: [] == no else statement, [NodeA, nodeB, ...] == else body
            before = copy.copy(global_vars) # snapshot
            # Build the test condition, substitute any variables
            condition = codegen.to_source(cur_orelse[0].test)
            for key in global_vars:
                condition = re.sub(key, global_vars[key], condition)

            # Visit body
            elif_visitor = Z3Visitor()
            for elem in cur_orelse[0].body:
                elif_visitor.visit(elem)

            after = copy.copy(global_vars)

            calculate_conditional_vars(before, after)

            after_var_sets[condition] = after

            # Iterate
            cur_orelse = cur_orelse[0].orelse

        # Else:
        # Deal with the else statement (possibly empty)
        before = copy.copy(global_vars)

        else_visitor = Z3Visitor()
        for elem in cur_orelse:
            else_visitor.visit(elem)

        after = copy.copy(global_vars)

        calculate_conditional_vars(before, after)

        # Add assertions to the solver equivalent to the if-elif-else conditions and their bodies
        for condition in after_var_sets:
            after_dic = after_var_sets[condition]

            #Build list of variables that would be equal if condition were true
            var_equivalencies = []
            for var in global_vars:
                if var in after_dic:
                    var_equivalencies.append(global_vars[var]+" == "+after_dic[var])
            var_equivalencies_str = ", ".join(var_equivalencies)

            # Assert that if the condition is true, the variables are equal
            exec("global_solver.add(z3.Implies("+condition+", z3.And("+var_equivalencies_str+")))")
            z3_calls.append("z3.Implies("+condition+", z3.And("+var_equivalencies_str+"))")

    def visit_IfExpr(self, node):
        """ 
        Visit an if-condition of the form: a if b else c
        """
        pass

    def visit_Expr(self, node):
        """ 
        Visit an expression, currently this function only looks at
        'requires(...)' and 'assures(...)' expressions. More soon!
        """
        # can probably optimize this function by merging both cases
        if isinstance(node.value, ast.Call) and \
            isinstance(node.value.func, ast.Name):
            if node.value.func.id == 'requires' or node.value.func.id == 'assures':
                # Uncompile 'bodyx' in 'requires/assures(body1, body2, ...) for all x
                for condition in node.value.args:
                    body = codegen.to_source(condition)

                    if node.value.func.id == 'assures':
                        for key in global_vars:
                            body = re.sub(key, global_vars[key], body)
                    # Add assersion to the global solver
                    eval("global_solver.add"+body)

                    z3_calls.append(body[1:-1])
        else:
            print ("Expr:", codegen.to_source(node))

    def visit_Assign(self, node):
        """
        Update/Add to the global variable dictionary and the global solver 
        to reflect the latest assignment
        """
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
                # Add to variable dictionary
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

    def visit_AugAssign(self, node):
        """
        Update/Add to the global variable dictionary and the global solver 
        to reflect the latest assignment
        """
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

    def visit_FunctionDef(self, node):
        """
        Declare parameters as z3 variables. Create new Z3Visitor to visit each 
        element in the functionDef body
        """

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
        pass


with open (sys.argv[1], "r") as myfile:
        data = myfile.read()


tree = ast.parse(data)
print ("------- original -------")
print (astpp.dump(tree))

# Visit AST and aggregate Z3 function calls
source_visitor = Z3Visitor()
source_visitor.visit(tree)

# Debug print-out calls
result = global_solver.check()
print ("RESULT:", result)

print ("vars\n", global_vars)

# print ("\nvars", len(z3_vars))
# for var in sorted(z3_vars):
#     print(var)

print ("\ncalls", len(z3_calls))
for call in z3_calls:
    print (call)
