import ast
import astpp
import sys
from ast import *
import imp
# import z3
# from z3 import *
# import codegen 
# from codegen import *

# Codegen
codegen = imp.load_source('codegen', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/codegen/codegen.py')

# Z3
sys.path.append('/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/')
z3 = imp.load_source('z3', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/z3.py')

s = z3.Solver()
# Dictionary containing the name of the user's variable as a key
# and a tuple of (z3 varibale name, value) as the value
# Where 'value' corresponds to the current value of the user's variable
# ie. (<user var> : (<z3 var>, <value>))
vars_py_to_z3 = {} 

z3_funcs = {}

Globals = {}

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

class AssertCmpTransformer(ast.NodeTransformer):
    """Transform 'assert a==b' into 'assert_equal(a, b)'
    """
    def visit_Assert(self, node):
        print ("Preforming AssertCmpTransformer")
        if isinstance(node.test, ast.Compare) and \
                len(node.test.ops) == 1 and \
                isinstance(node.test.ops[0], ast.Eq):
            call = ast.Call(func=ast.Name(id='assert_equal', ctx=ast.Load()),
                            args=[node.test.left, node.test.comparators[0]],
                            keywords=[])
            # Wrap the call in an Expr node, because the return value isn't used.
            newnode = ast.Expr(value=call)
            ast.copy_location(newnode, node)
            ast.fix_missing_locations(newnode)
            print ("SUCCESSFUL ASSERT")
            return newnode
        
        # Return the original node if we don't want to change it.
        return node

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

class Z3Visitor(ast.NodeVisitor):

    def visit_Expr(self, node):
        # check for 'requires(...)
        if isinstance(node.value, ast.Call) and \
            isinstance(node.value.func, ast.Name):
            if node.value.func.id == 'requires':
                # Uncompile the body of 'requires(body)'. Call s.add(body)
                # Currenly only handles a single call in 'body', though handling
                # multiple arguments is possible. eg. assures(body1, body2, ...)
                body = codegen.to_source(node.value.args[0])
                x = z3.Int('x') # Need to get this dynamically
                eval("s.add("+body+")")

                print ("Expr (req):", codegen.to_source(node))

            elif node.value.func.id == 'assures':
                # Uncompile the body of 'requires(body)'. Call s.add(body)
                body = codegen.to_source(node.value.args[0])
                x = z3.Int('x')
                eval("s.add("+body+")")

                print ("Expr (ass):", codegen.to_source(node))
        else:
            print ("Expr:", codegen.to_source(node))

    ''' Will be used to execute z3 ...'''
    def visit_Assign(self, node):
        print ("Assignment:", codegen.to_source(node))

    ''' Will be used to check for calls to functions we have instantiated z3
        equivalents to, and call those equivalents with the given arguments'''
    def visit_Call(self, node):
        print ("Call:", codegen.to_source(node))

    def visit_FunctionDef(self, node):
        
        print ("Func:", codegen.to_source(node))
        mylocals = {}
        arg_list = get_func_args(node)
        for arg in arg_list:
            # Define each parameter. (Need to check if already declared in global scope?)
            exec(arg+" = z3.Int('"+arg+"')")
            # Add variable to global scope dictionary (make local?)

        # x = z3.Int('x')

        # create z3 function def (need to dynamically fill in parameters)
        # how to infer return type?
        f = z3.Function('f', z3.IntSort(), z3.IntSort(), z3.IntSort())
        return_node = get_return(node)

        # Post-condition using function body
        # if var in post cond is modified in funciton (ie. assigned new val)
        # then substitute assignment for var in post condition
        # assures(x > 0) and x = x - 5:
        s.add(x - 5 > 0)

        # use this to visit function body and build z3 representation
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
print ("satisfiable:", result)

if (result):
    pass
    # m = s.model()
    # print(m)
    # print ("f(x) =", m.evaluate(f(x, y))) # f out of scope (use global dictionary?)

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