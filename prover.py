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

    def __init__(self, var_dictionary, var_ref_dictionary, z3_solver):
        self.local_vars = var_dictionary # variable reference dictionary - all variable (including incremented)
        self.which = var_ref_dictionary # Which incremented var corresponds to its z3 var
        self.solver = z3_solver

    def visit_If(self, node):

        # rebuild the condition with variable substitution from local_vars
        condition = codegen.to_source(node.test)
        for key in self.which:
            condition = re.sub(key, self.local_vars[self.which[key]], condition)

        # Create a visitor to visit the if-condition, and maybe its body
        if_visitor = Z3Visitor(self.local_vars, self.which, copy.copy(self.solver)) # THIS COPY FAILS - THUS THIS WHOLE MEATHOD FAILS
        if_visitor.sol = copy.copy(self.solver) 
        eval("if_visitor.sol.add"+condition)

        # If the if-condition is true, visit the body
        if str(if_visitor.sol.check()) == 'sat':
            # Visit body
            for elem in node.body:
                if_visitor.visit(elem)

            # Update class info
            self.solver = if_visitor.sol # Add any z3 calls that might have been made in the body
            self.local_vars.update(if_visitor.local_vars) # Add any new variable
            self.which.update(if_visitor.which) # Update the current version of each variable
            return # Do not bother reading any following elif/else conditions

        # Loop over elifs (if any) until we find a satisfiable one.
        cur_orelse = node.orelse
        while len(cur_orelse) == 1 and isinstance(cur_orelse[0], ast.If): # i.e. another elif. other possibilities: [] == no else statement, [NodeA, nodeB, ...] == else body
            print("**********\ncur_orelse", cur_orelse)
            # Having to index into a list like this is terrible, clean up later
            # Build the test condition, substitute any variables
            condition = codegen.to_source(cur_orelse[0].test)
            for key in self.which:
                condition = re.sub(key, self.local_vars[self.which[key]], condition)

            # Create solver, check condition, execute body if condition is true - same as above with If
            elif_visitor = Z3Visitor(self.local_vars, self.which, self.solver)

            if str(elif_visitor.solver.check()) == 'unsat':
                print("not solvable even before adding condition")

            eval("elif_visitor.solver.add"+condition)
            print("elif_visitor.solver.add"+condition)
            if str(elif_visitor.solver.check()) == 'sat':
                print("visiting body")
                # Visit body
                for elem in cur_orelse[0].body:
                    elif_visitor.visit(elem)

                # Update class attributes
                self.solver = elif_visitor.solver # Add any z3 calls that might have been made in the body
                self.local_vars.update(elif_visitor.local_vars) # Add any new variable
                self.which.update(elif_visitor.which) # Update the current version of each variable
                return # Do not bother reading any following elif/else conditions

            # Iterate
            cur_orelse = cur_orelse[0].orelse

        # Deal with the else statement (possibly empty)
        else_visitor = Z3Visitor(self.local_vars, self.which, self.solver)
        print("else", cur_orelse)
        for elem in cur_orelse:
            else_visitor.visit(elem)

        # Update class attributes
        self.solver = else_visitor.solver # Add any z3 calls that might have been made in the body
        self.local_vars.update(else_visitor.local_vars) # Add any new variable
        self.which.update(else_visitor.which) # Update the current version of each variable


    def visit_IfExpr(self, node):
        pass
        # An expression such as a if b else c
    
    def visit_For(self, node):
        pass
    
    def visit_While(self, node):
        pass

    def visit_Expr(self, node):
        # check for 'requires(...)' and 'assures(...)''
        # can probablt optimize this function by merging both cases
        if isinstance(node.value, ast.Call) and \
            isinstance(node.value.func, ast.Name):
            if node.value.func.id == 'requires':
                # Uncompile 'bodyx' in 'requires(body1, body2, ...) for all x
                for condition in node.value.args:
                    body = codegen.to_source(condition)
                    # self.z3_calls.append("s.add"+body)
                    eval("self.solver.add"+body)
                    print ("s.add"+body)

            elif node.value.func.id == 'assures':
                # Uncompile 'bodyx' in 'assures(body1, body2, ...) for all x
                for condition in node.value.args:
                    body = codegen.to_source(condition)

                    # Substitute variables in body with the corresponding value
                    # found in the global variable dictionary
                    for key in self.which:
                        body = re.sub(key, self.local_vars[self.which[key]], body)

                    eval("self.solver.add"+body)
                    # self.z3_calls.append("s.add"+body)
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
        for key in self.which:
            # substitute any variables with their present values
            body = re.sub(key, "("+self.local_vars[self.which[key]]+")", body)

        for target in targets:
            if target not in self.which: # new variable
                self.which[target] = target
                self.local_vars[target] = body
                exec("global "+target)
                exec(target+" = z3.Int('"+target+"')", globals())

            else: # existing variable
                cur = self.which[target]
                # create a new incremented variable based off of 'target'
                incremented = cur[:1] + str(eval(cur[1:]+ "+ 1"))
                # Add it to the variable dictionary, along with value
                self.local_vars[incremented] = body
                # update which var refers to target (update which)
                self.which[target] = incremented

    ''' Will be used to check for calls to functions we have instantiated z3
        equivalents to, and call those equivalents with the given arguments'''

    def visit_AugAssign(self, node):
        old_val = self.local_vars[self.which[node.target.id]]
        mod_val = codegen.to_source(node.value)

        # Rebuild RHS: Substitute the dictionary value of each variable
        for key in self.which:
            # substitute any variables with their present values
            mod_val = re.sub(key, "("+str(self.local_vars[self.which[key]])+")", mod_val)

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

        # Calculate and add the new value to the local dictionary
        new_val = "("+str(old_val)+") "+operator+" ("+str(mod_val)+")"

        target = self.which[node.target.id]
        # Create a new incremented variable based off of 'target'
        incremented = target[:1] + str(eval(target[1:]+ "+ 1"))
        # Add it to the variable dictionary, along with value
        self.local_vars[incremented] = new_val
        # update which var refers to the target (update which)
        self.which[node.target.id] = incremented

    def visit_Call(self, node):
        pass
        # print ("Call:", codegen.to_source(node))

    def visit_FunctionDef(self, node):
        
        # print ("Func:", codegen.to_source(node)) # This blows up for some reason

        arg_list = get_func_args(node)

        for arg in arg_list:
            # Declare each parameter as a global variable
            exec("global "+arg)
            exec(arg+" = z3.Int('"+arg+"')", globals())

            # Add the parameter to our global variable dictionary
            self.local_vars[arg] = arg
            self.which[arg] = arg

        # create z3 function def (need to dynamically fill in parameters)
        # how to infer return type?
        # f = z3.Function('f', z3.IntSort(), z3.IntSort(), z3.IntSort())
        # exec(node.name+" = z3.Funciton('"node.name"', "+" z3.IntSort(),"*len(arg_list)+"return")
        # return_node = get_return(node)

        # Visit function body and build z3 representation
        func_visitor = Z3Visitor(self.local_vars, self.which, self.solver)
        for elem in node.body:
            func_visitor.visit(elem)

        # self.z3_calls += func_visitor.get_Z3_Calls()

    def visit_Return(self, node):
        print ("Return:", codegen.to_source(node))

    # Bother having a getter method? 
    def get_Z3_Calls(self):
        return self.z3_calls


with open (sys.argv[1], "r") as myfile:
        data = myfile.read()


tree = ast.parse(data)
print ("------- original -------")
print (astpp.dump(tree))

# Visit AST and aggregate Z3 function calls
my_visitor = Z3Visitor({}, {}, z3.Solver())
my_visitor.visit(tree)

print ("which:") 
# pprint (which)
# sorted( ((v,k) for k,v in self.which.iteritems()))
pretty_print_dic(my_visitor.which)

print ("local_vars:") 
pretty_print_dic(my_visitor.local_vars)

result = my_visitor.solver.check()
print ("RESULT:", result)

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