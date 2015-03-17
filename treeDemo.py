from tree import Tree

(_ROOT, _DEPTH, _BREADTH) = range(3)

tree = Tree()

# Create a root. Add assertion to the assertion list. Add definition of 'x'
tree.add_node("Root")
tree["Root"].add_assertion("x != 99")
tree.update_var("Root", "x", "x")

# Create child node. Update 'x' locally. Add assertion locally
tree.add_node("Child 1", "Root")
tree.update_var("Child 1", "x", "x * 99")
tree["Child 1"].add_assertion("x > 5")

# Add child to first child. 
# tree.add_node("Child 2", "Child 1")
# Update 'x' at child 1 level. changes propogate down to child 2
tree.update_var("Child 1", "x", "x - 11")
# Update 'x' at child 1 level. changes DO NOT propogate down to child 2
# tree.update_var("Child 1", "x", "x + 13", recursive=False)

# Update 'x' for all nodes
tree.update_var("Root", "x", "x + 5")

print("***** NODES *****")
tree.print_nodes()
