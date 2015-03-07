import ast
import astpp
import sys
from ast import *
import imp
import re
# import z3
# from z3 import *
# import codegen 
# from codegen import *

# Codegen
codegen = imp.load_source('codegen', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/codegen/codegen.py')

# Z3
sys.path.append('/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/')
z3 = imp.load_source('z3.py', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/z3.py')

s = z3.Solver()
# Dictionary containing the name of the user's variable as a key
# and a tuple of (z3 varibale name, value) as the value
# Where 'value' corresponds to the current value of the user's variable
# ie. (<user var> : (<z3 var>, <value>))
vars_py_to_z3 = {} 

z3_funcs = {}


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

''' Unnecessary - remove later'''
class RequiresTransformer(ast.NodeTransformer):

    '''Transform 'requires(...)' into 's.add(...)' '''
    def visit_Expr(self, node):
        if (node.value, ast.Call) and \
            isinstance(node.value.func, ast.Name) and \
            node.value.func.id == 'requires':
            # Making 's.add(...)' node
            newnode = ast.Expr(ast.Call(func=ast.Attribute(
                value=ast.Name(id='s', ctx=ast.Load()), attr='add', ctx=ast.Load()),
                    # copying '...' (ie. filling in body with body of old node)
                    args=node.value.args,
                    keywords=node.value.keywords, 
                    starargs=node.value.starargs, 
                    kwargs=node.value.kwargs))
            ast.copy_location(newnode, node)
            ast.fix_missing_locations(newnode)
            return newnode
        # Return the original node if we don't want to change it.
        return node

''' That main thing '''
class Z3Visitor(ast.NodeVisitor):

    def visit_Expr(self, node):
        # check for 'requires(...)
        if isinstance(node.value, ast.Call) and \
            isinstance(node.value.func, ast.Name):
            if node.value.func.id == 'requires':
                # Uncompile 'bodyx' in 'requires(body1, body2, ...) for all x
                for condition in node.value.args:
                    body = codegen.to_source(condition)
                    eval("s.add"+body)
                    print ("s.add"+body)

            elif node.value.func.id == 'assures':
                # Uncompile 'bodyx' in 'assures(body1, body2, ...) for all x
                for condition in node.value.args:
                    body = codegen.to_source(condition)

                    # Substitute variables in body with the corresponding value
                    # found in the global variable dictionary
                    for key in vars_py_to_z3:
                        body = re.sub(re.compile(key), vars_py_to_z3[key], body)

                    eval("s.add"+body)
                    print ("s.add"+body)
        else:
            print ("Expr:", codegen.to_source(node))

    ''' Update/Add to the vars_py_to_z3 dictionary to reflect the latest assignment'''
    def visit_Assign(self, node):
        print ("Assignment:", codegen.to_source(node))

        targets = node.targets[0] # left hand side (Name or Tuple obj)
        value = node.value # right hand side

        if isinstance(targets, ast.Tuple): # multiple targets
            for target in targets.elts:
                if target.id not in vars_py_to_z3: # add
                    vars_py_to_z3[target.id] = codegen.to_source(node.value)
                else: # update
                    old_val = vars_py_to_z3[target.id] 
                    new_val = codegen.to_source(node.value)
                    updated_val = re.sub(re.compile(target.id), "("+new_val+")", old_val)
                    vars_py_to_z3[target.id] = updated_val

        else : # only one target
            old_val = vars_py_to_z3[targets.id] 
            new_val = codegen.to_source(node.value)
            updated_val = re.sub(re.compile(targets.id), "("+new_val+")", old_val)
            
            vars_py_to_z3[targets.id] = updated_val

    ''' Will be used to check for calls to functions we have instantiated z3
        equivalents to, and call those equivalents with the given arguments'''
    def visit_Call(self, node):
        print ("Call:", codegen.to_source(node))

    def visit_FunctionDef(self, node):
        
        print ("Func:", codegen.to_source(node))

        arg_list = get_func_args(node)

        for arg in arg_list:
            # Declare each parameter as a global variable
            exec("global "+arg)
            exec(arg+" = z3.Int('"+arg+"')", globals())

            # Add the parameter to our global variable dictionary
            vars_py_to_z3[arg] = arg

        # create z3 function def (need to dynamically fill in parameters)
        # how to infer return type?
        # f = z3.Function('f', z3.IntSort(), z3.IntSort(), z3.IntSort())
        # exec(node.name+" = z3.Funciton('"node.name"', "+" z3.IntSort(),"*len(arg_list)+"return")
        # return_node = get_return(node)

        # Visit function body and build z3 representation
        for elem in node.body:
            Z3Visitor().visit(elem)

    def visit_Return(self, node):
        print ("Return:", codegen.to_source(node))

with open (sys.argv[1], "r") as myfile:
        data = myfile.read()


tree = ast.parse(data)
print ("------- original -------")
print (astpp.dump(tree))

# tree = RequiresTransformer().visit(tree)
# print ("------- z3 tree -------")
# print (astpp.dump(tree))

# Visit AST and preform Z3 function calls
Z3Visitor().visit(tree)

result = s.check()
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
////////////////// NOTES ON THIS SCRIPT /////////////////////
In the users code, Pre and Post-conditions must be declared after the function
definition line (def f(x):), because the z3 variables referenced in the 
pre/post condition calls are instantiated when the function def line is parsed


'''