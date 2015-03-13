import ast
import astpp
import sys
from ast import *
import imp
import re
from pprint import pprint
from operator import itemgetter
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

local_vars = {} # variable reference dictionary - all variable (including incremented)
which = {} # Which incremented var corresponds to its z3 var

# Scoping idea: for each scope have a 'which' dictionary, have a 'meta_which' dictionary
# that keeps track of which 'which' dictionary you are using in that moment.

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

''' That main thing '''
class Z3Visitor(ast.NodeVisitor):

    def visit_Expr(self, node):
        # check for 'requires(...)' and 'assures(...)''
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
                    for key in which:
                        body = re.sub(key, local_vars[which[key]], body)

                    eval("s.add"+body)
                    print ("s.add"+body)
        else:
            print ("Expr:", codegen.to_source(node))


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
        for key in which:
            # substitute any variables with their present values
            body = re.sub(key, "("+local_vars[which[key]]+")", body)

        for target in targets:
            if target not in which: # new variable
                which[target] = target
                local_vars[target] = body
                exec("global "+target)
                exec(target+" = z3.Int('"+target+"')", globals())

            else: # existing variable
                cur = which[target]
                # create a new incremented variable based off of 'target'
                incremented = cur[:1] + str(eval(cur[1:]+ "+ 1"))
                # Add it to the variable dictionary, along with value
                local_vars[incremented] = body
                # update which var refers to target (update which)
                which[target] = incremented

    def visit_AugAssign(self, node):
        pass

    ''' Update/Add to the local_vars dictionary to reflect the latest assignment'''
    def visit_Assign_Old(self, node):
        pass
        # print ("Assignment:", codegen.to_source(node))

        # LHS = node.targets[0] # left hand side (Name or Tuple obj)
        # RHS = node.value # right hand side

        # # Create a list of targets
        # targets = []
        # if isinstance(LHS, ast.Tuple): # multiple targets
        #     for target in LHS.elts:
        #         targets.append(target.id)
        # else:                          # one target
        #     targets.append(LHS.id)

        # # Rebuild RHS: Substitute the dictionary value of each variable into the RHS
        # new_val = codegen.to_source(RHS) 
        # for var in local_vars:
        #     new_val = re.sub(var, "("+local_vars[var]+")", new_val)
        
        # # For each target add the new value to the local dictionary 
        # for target in targets: 
        #     local_vars[target] = str(eval(new_val))

    ''' Will be used to check for calls to functions we have instantiated z3
        equivalents to, and call those equivalents with the given arguments'''

    def visit_AugAssign(self, node):
        pass
        old_val = local_vars[which[node.target.id]]
        mod_val = codegen.to_source(node.value)

        # Rebuild RHS: Substitute the dictionary value of each variable
        for key in which:
            # substitute any variables with their present values
            mod_val = re.sub(key, "("+str(local_vars[which[key]])+")", mod_val)

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

        target = which[node.target.id]
        # Create a new incremented variable based off of 'target'
        incremented = target[:1] + str(eval(target[1:]+ "+ 1"))
        # Add it to the variable dictionary, along with value
        local_vars[incremented] = new_val
        # update which var refers to the target (update which)
        which[node.target.id] = incremented

    def visit_Call(self, node):
        print ("Call:", codegen.to_source(node))

    def visit_FunctionDef(self, node):
        
        # print ("Func:", codegen.to_source(node)) # This blows up for some reason

        arg_list = get_func_args(node)

        for arg in arg_list:
            # Declare each parameter as a global variable
            exec("global "+arg)
            exec(arg+" = z3.Int('"+arg+"')", globals())

            # Add the parameter to our global variable dictionary
            local_vars[arg] = arg
            which[arg] = arg

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

# Visit AST and preform Z3 function calls
Z3Visitor().visit(tree)

print ("which:") 
# pprint (which)
# sorted( ((v,k) for k,v in which.iteritems()))
pretty_print_dic(which)

print ("local_vars:") 
pretty_print_dic(local_vars)

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

'''