# by Brett Kromkamp 2011-2014 (brett@youprogramming.com)
# You Programming (http://www.youprogramming.com)
import sys
import imp
import re
import copy

sys.path.append('/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/')
z3 = imp.load_source('z3.py', '/Library/Frameworks/Python.framework/Versions/3.4/lib/Python3.4/z3/bin/z3.py')

class Node:
    def __init__(self, identifier):
        self.__identifier = identifier
        self.__children = []
        self.__local_vars = {}
        self.__which = {}
        self.__assertions = []

    @property
    def identifier(self):
        return self.__identifier

    @property
    def children(self):
        return self.__children

    @property
    def local_vars(self):
        return self.__local_vars

    @property
    def which(self):
        return self.__which

    @property
    def assertions(self):
        return self.__assertions

    def add_child(self, identifier):
        self.__children.append(identifier)

    def add_assertion(self, assertion):
        self.__assertions.append(assertion)

    def set_which(self, which_dic):
        self.__which = copy.copy(which_dic)

    def set_local_vars(self, local_vars_dic):
        self.__local_vars = copy.copy(local_vars_dic)

    def set_assertions(self, assertions):
        self.__assertions = copy.copy(assertions)

    def update_var(self, variable, value):
        updated_value = value
        for key in self.__which:
            # substitute any variables with their present values
            # TODO: create more elegant way to get current var. not self.__local_vars[self.__which[key]]
            updated_value = re.sub(key, "("+self.__local_vars[self.__which[key]]+")", updated_value)

        if variable not in self.__which: # new variable
                self.__which[variable] = updated_value
                self.__local_vars[variable] = updated_value
        else: # Exsiting var
            cur_var = self.__which[variable]
            # create a new incremented variable based off of 'variable'
            incremented = cur_var[:1] + str(eval(cur_var[1:]+ "+ 1"))
            # Add it to the variable dictionary, along with updated_value
            self.__local_vars[incremented] = updated_value
            # update which var refers to variable (update which)
            self.__which[variable] = incremented

    def is_satisfiable(self):
        solver = z3.Solver()
        
        for assertion in self.__assertions:
            eval("solver.add("+assertion+")")
        
        result = str(solver.check())
        if result == 'sat':
            return True
        else: 
            return False


