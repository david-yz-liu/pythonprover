
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
Create z3 representation of a function definition - to be used for Call Nodes
    - Do one pass over function definitions to generate z3 declarations
Handle recursive calls
    - 
if statements
    - Optimize: Use z3.If() function to represent if-else-block instead of z3.Or() 
Find a way out of hard indexing into orelse nodes in an ast.if Node
Change way if-expressions are handled - currently only accessable from with visit_Assign
Call Nodes are sometimes wrapped in Expr Nodes. Find a way to call self.visit_Call
from inside visit_Expr

'''

import ast
from ast import *
import astpp
import sys
import re
import copy
from pprint import pprint
from operator import itemgetter

import z3
from z3 import *

import codegen
from codegen import *

# init("z3.dll")

# The solver in which all z3 assertions go
global_solver = z3.Solver()
# Dictionary that keeps track of the current version of a variable
# e.g. {x : x, y : y3}
global_vars = {}
local_vars = {}

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
            local_vars[key] = incremented
            # Declare new z3 variable
            exec("global "+incremented)
            exec(incremented+" = z3.Int('"+incremented+"')", globals())
            # Give it the two possible values
            exec("global_solver.add(z3.Or("+incremented+" == "+before[key]+", "+incremented+" == "+after[key]+"))")

            # Track new vars and assertions for debugging purposes
            z3_vars.append(incremented)
            z3_calls.append("Or("+incremented+" == "+before[key]+", "+incremented+" == "+after[key]+")")

class Z3FunctionVisitor(ast.NodeVisitor):

    def visit_FunctionDef(self, node):
        """
        Reads the function definition (but not the body!) and declares the function
        and its parameters as z3 variables.
        This function assumes that each parameter is an Int and each function 
        returns an Int
        """

        arg_list = []
        for elem in node.args.args:
            arg_list.append(elem.arg)

        for arg in arg_list:
            # Declare each parameter as a global variable
            if arg not in global_vars: # New variable
                global_vars[arg] = arg
                exec("global "+arg)
                exec(arg+" = z3.Int('"+arg+"')", globals())
                z3_vars.append(arg)

        params_str = "IntSort(), "*len(arg_list)
        exec(node.name+" = z3.Function('"+node.name+"', "+params_str+"IntSort())", globals())

class Z3Visitor(ast.NodeVisitor):
    """
    The main thing! Reads over an AST and determines if the program the AST 
    represents is satisfiable.
    """

    def visit_For(self, node):
        # target, iter, body, orelse
        print("For node:")
        print("\ttarget.id", node.target.id)    
        print("\titer", node.iter)
        print("\tbody", node.body)
        print("\torelse", node.orelse)
        print()

    def visit_While(self, node):
        pass

    def visit_Call(self, node):
        # class Call(
        print ("Class node: ")
        print ("\tfunc", node.func)
        print ("\targs", node.args)
        print ("\tkeywords", node.keywords)
        print ("\tstarargs", node.starargs)
        print ("\tkwargs", node.kwargs)
        print ()

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
        for key in local_vars:
            condition = re.sub(key, local_vars[key], condition)

        # Take a snapshot of the variable set before entering the if-elif-else block
        before = copy.copy(local_vars) # snapshot
        
        # Create a visitor to visit the if-block
        if_visitor = Z3Visitor()
        # Visit body
        for elem in node.body:
            if_visitor.visit(elem)

        # Take a snapshot of the variable set after exiting the if-elif-else block
        after = copy.copy(local_vars) # snapshot 
        
        calculate_conditional_vars(before, after)

        after_var_sets[condition] = after

        # Elifs:
        # Loop over elifs (if any) until we find a satisfiable one.
        cur_orelse = node.orelse
        while len(cur_orelse) == 1 and isinstance(cur_orelse[0], ast.If): # i.e. another elif. other possibilities: [] == no else statement, [NodeA, nodeB, ...] == else body
            before = copy.copy(local_vars) # snapshot
            # Build the test condition, substitute any variables
            condition = codegen.to_source(cur_orelse[0].test)
            for key in local_vars:
                condition = re.sub(key, local_vars[key], condition)

            # Visit body
            elif_visitor = Z3Visitor()
            for elem in cur_orelse[0].body:
                elif_visitor.visit(elem)

            after = copy.copy(local_vars)

            calculate_conditional_vars(before, after)

            after_var_sets[condition] = after

            # Iterate
            cur_orelse = cur_orelse[0].orelse

        # Else:
        # Deal with the else statement (possibly empty)
        before = copy.copy(local_vars)

        else_visitor = Z3Visitor()
        for elem in cur_orelse:
            else_visitor.visit(elem)

        after = copy.copy(local_vars)

        calculate_conditional_vars(before, after)

        # Add assertions to the solver equivalent to the if-elif-else conditions and their bodies
        for condition in after_var_sets:
            after_dic = after_var_sets[condition]

            #Build list of variables that would be equal if condition were true
            var_equivalencies = []
            for var in local_vars:
                if var in after_dic:
                    var_equivalencies.append(local_vars[var]+" == "+after_dic[var])
            var_equivalencies_str = ", ".join(var_equivalencies)

            # Assert that if the condition is true, the variables are equal
            exec("global_solver.add(z3.Implies("+condition+", z3.And("+var_equivalencies_str+")))")
            z3_calls.append("z3.Implies("+condition+", z3.And("+var_equivalencies_str+"))")

    def visit_IfExp(self, node):
        """ 
        Visit an if-condition of the form: a if b else c
        Currently called only from visit_Assign and returns to there.
        Makes no z3 calls of its own
        """
        # rebuild the condition with variable substitution from local_vars
        condition = codegen.to_source(node.test)
        for key in local_vars:
            condition = re.sub(key, local_vars[key], condition)
        
        # Assemble 'else' body
        if_body = codegen.to_source(node.body)
        for key in local_vars:
            # substitute any variables with their present incremented variable
            if_body = re.sub(key, local_vars[key], if_body)
        
        # Assemble 'if' body
        else_body = codegen.to_source(node.orelse)
        for key in local_vars:
            # substitute any variables with their present incremented variable
            else_body = re.sub(key, local_vars[key], else_body)

        return [condition, if_body, else_body]
            
    def visit_Expr(self, node):
        """ 
        Visit an expression, currently this function only looks at
        'requires(...)' and 'assures(...)' expressions. More soon!
        """
        print("Expr node: {0}".format(node.value))
        if isinstance(node.value, ast.Call):
            print("Call node {0} \n \targs: {1}\n\t{2}, {3}, {4}".format(node.value.func.id, node.value.args, node.value.keywords, node.value.starargs, node.value.kwargs))
            # class Call(func, args, keywords, starargs, kwargs)
            # consider moving this case entirely to visit_call
            if isinstance(node.value.func, ast.Name):
                if node.value.func.id == 'requires' or node.value.func.id == 'assures':
                    # Uncompile 'bodyx' in 'requires/assures(body1, body2, ...) for all x
                    for condition in node.value.args:
                        body = codegen.to_source(condition)

                        if node.value.func.id == 'assures':
                            for key in local_vars:
                                body = re.sub(key, local_vars[key], body)
                        # Add assersion to the global solver
                        eval("global_solver.add"+body)

                        z3_calls.append(body[1:-1])
            else: # function call
                # call/apply z3 representation of this function
                temp_visitor = Z3Visitor()
                temp_visitor.visit(node.value)



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

        if isinstance(RHS, ast.IfExp):
            ifExp_visitor = Z3Visitor() 
            cond_if_else = (ifExp_visitor.visit(RHS))
            print("RHS is ifExp")
            cond = cond_if_else[0]
            if_body = cond_if_else[1]
            else_body = cond_if_else[2]

            for target in targets:
                if target not in local_vars: # New variable
                    # Add to variable dictionary
                    local_vars[target] = target

                    exec("global "+target)
                    exec(target+" = z3.Int('"+target+"')", globals())
                    exec("global_solver.add(z3.Or("+target+" == "+if_body+","+target+" == "+else_body+"))")

                    z3_vars.append(target)
                    z3_calls.append("Or("+target+" == "+if_body+","+target+" == "+else_body+"))")

                else: # Existing variable
                    cur_var = local_vars[target]
                    # create a new incremented variable based off of 'target'
                    incremented = cur_var[:1] + str(eval(cur_var[1:]+ "+ 1"))
                    # Update variable dictionary
                    local_vars[target] = incremented

                    # Declare incremented as z3 object
                    exec("global "+incremented)
                    exec(incremented+" = z3.Int('"+incremented+"')", globals())
                    # Declare the new variable's relationship with its predecessor
                    exec("global_solver.add(z3.Or("+target+" == "+if_body+","+target+" == "+else_body+"))")

                    z3_vars.append(incremented)
                    z3_calls.append("Or("+target+" == "+if_body+","+target+" == "+else_body+"))")

            return
        elif isinstance(RHS, ast.Call):
            temp_visitor = Z3Visitor()
            temp_visitor.visit(RHS)

            # print("Error: Assignment from function calls not yet supported")

        elif isinstance(RHS, ast.UnaryOp):
            print("Error: Assignment from unary expressions not yet supported")
            return
        # Otherwise RHS is a Name, Num or Binop

        # assemble the right hand side of the assignment
        body = codegen.to_source(RHS)
        for key in local_vars:
            # substitute any variables with their present incremented variable
            body = re.sub(key, local_vars[key], body)

        for target in targets:
            if target not in local_vars: # New variable
                # Add to variable dictionary
                local_vars[target] = target

                exec("global "+target)
                exec(target+" = z3.Int('"+target+"')", globals())
                exec("global_solver.add("+target+" == "+body+")")

                z3_vars.append(target)
                z3_calls.append(target+" == "+body)

            else: # Existing variable
                cur_var = local_vars[target]
                # create a new incremented variable based off of 'target'
                incremented = cur_var[:1] + str(eval(cur_var[1:]+ "+ 1"))
                # Update variable dictionary
                local_vars[target] = incremented

                # Declare incremented as z3 object
                exec("global "+incremented)
                exec(incremented+" = z3.Int('"+incremented+"')", globals())
                # Declare the new variable's relationship with its predecessor
                print("global_solver.add("+incremented+" == "+body+")")
                exec("global_solver.add("+incremented+" == "+body+")")

                z3_vars.append(incremented)
                z3_calls.append(incremented+" == "+body)

    def visit_AugAssign(self, node):
        """
        Update/Add to the global variable dictionary and the global solver 
        to reflect the latest assignment
        """
        target = node.target.id
        cur_var = local_vars[node.target.id] # The current incremented variable representing target

        RHS = codegen.to_source(node.value)
        # Rebuild RHS: Substitute the dictionary value of each variable
        for key in local_vars:
            # substitute any variables with their present values
            RHS = re.sub(key, local_vars[key], RHS)

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
        local_vars[target] = incremented
        # Declare incremented as z3 object
        exec("global "+incremented)
        exec(incremented+" = z3.Int('"+incremented+"')", globals())
        # Declare the new variable's relationship with its predecessor
        exec("global_solver.add("+incremented+" == "+body+")")

        z3_vars.append(incremented)
        z3_calls.append(incremented+" == "+body)

    def visit_FunctionDef(self, node):
        """
        Declare parameters as z3 variables. Create new Z3Visitor to visit each 
        element in the functionDef body. 
        """
        global local_vars
        local_vars = copy.copy(global_vars)

        # Visit function body and build z3 representation
        func_visitor = Z3Visitor()
        for elem in node.body:
            func_visitor.visit(elem)

        after = local_vars

        # get return variable
        # represent it in terms of before variables
        return_val = None
        # TODO: Make this find all returns in a function
        if isinstance(node.body[-1], ast.Return):
            # this assumes return_val is variable, not expression
            # TODO: handle expressions (or other types) in return
            return_val = local_vars[node.body[-1].value.id]

            arg_list = []
            for elem in node.args.args:
                arg_list.append(elem.arg)

            arg_list_str = ", ".join(arg_list)

            print ("global_vars\n", global_vars)
            print ("local_vars\n", local_vars)

            # global_solver.add(ForAll(['x', 'y'], f(x, y) == x1))

            print("global_solver.add(ForAll(["+arg_list_str+"], "+node.name+"("+arg_list_str+") == "+return_val+"))")
            exec("global_solver.add(ForAll(["+arg_list_str+"], "+node.name+"("+arg_list_str+") == "+return_val+"))")


        # Reset variables
        # local_vars = copy.copy(global_vars)
        # TODO: this way restarts the variables from x1, y1 etc
        # we will get conflicting assertions about them if we have more than one funciton def
        # need to keep iterating where we left off, but divorce any relation to
        # iterated vars used in prior funcitons

    def visit_Return(self, node):
        pass


with open (sys.argv[1], "r") as myfile:
        data = myfile.read()


tree = ast.parse(data)
print ("------- Abstract Syntax Tree -------")
print (astpp.dump(tree))

# visit AST and create z3 definitions of each function in the source
function_visitor = Z3FunctionVisitor()
function_visitor.visit(tree)

# Visit AST and aggregate Z3 function calls
source_visitor = Z3Visitor()
source_visitor.visit(tree)

print ("------- Debug print-out -------") 
result = global_solver.check() 
print ("RESULT:", result)

print ("global_vars\n", global_vars)
print ("local_vars\n", local_vars)

# print ("\nvars", len(z3_vars))
# for var in sorted(z3_vars):
#     print(var)

print ("\ncalls", len(z3_calls))
for call in z3_calls:
    print (call)
