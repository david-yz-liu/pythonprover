
# Brett Kromkamp (brett@youprogramming.com)
# You Programming (http://www.youprogramming.com)
# May 03, 2014

from node import Node

(_ROOT, _DEPTH, _BREADTH) = range(3)


class Tree:

    def __init__(self):
        self.__nodes = {}
        self.__root = None

    def __getitem__(self, key):
        return self.__nodes[key]

    def __setitem__(self, key, item):
        self.__nodes[key] = item

    @property
    def nodes(self):
        return self.__nodes

    def print_nodes(self):
        for key in self.__nodes:
            node = self[key]
            print("\n{0} : \nAssertions: {1}\nCurrent variables :{2}\nLocal variables: {3}" \
                .format(key, node.assertions, node.which, node.local_vars))

    def add_node(self, identifier, parent=None):
        node = Node(identifier)
        self[identifier] = node

        if parent is not None: # or just: 'if parent' ?
            self[parent].add_child(identifier)
            self[identifier].set_which(self[parent].which)
            self[identifier].set_assertions(self[parent].assertions)
            self[identifier].set_local_vars(self[parent].local_vars)
        else:
            self.__root = identifier

        return node

    def display(self, identifier, depth=_ROOT):
        children = self[identifier].children
        if depth == _ROOT:
            print("{0}".format(identifier))
        else:
            print("\t"*depth, "{0}".format(identifier))

        depth += 1
        for child in children:
            self.display(child, depth)  # recursive call

    def update_var(self, node, variable, value, recursive=True):
        if not node:
            # Error msg?
            return

        # Update current node
        self[node].update_var(variable, value)
        
        if recursive: # Recurse through children
            for identifier in self[node].children:
                self[identifier].update_var(variable, value)

    def traverse(self, identifier, mode=_DEPTH):
        # Python generator. Loosly based on an algorithm from 
        # 'Essential LISP' by John R. Anderson, Albert T. Corbett, 
        # and Brian J. Reiser, page 239-241
        yield identifier
        queue = self[identifier].children
        while queue:
            yield queue[0]
            expansion = self[queue[0]].children
            if mode == _DEPTH:
                queue = expansion + queue[1:]  # depth-first
            elif mode == _BREADTH:
                queue = queue[1:] + expansion  # width-first
