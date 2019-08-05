from z3 import *


def is_transitive(node1, node2, graph):
    transitivity_found = False
    for connectedNode in graph[node1]:
        if connectedNode == node2:
            transitivity_found = True
            break
        else:
            transitivity_found = is_transitive(connectedNode, node2, graph)
    return transitivity_found


def create_closure_set(node, original_graph, closure_graph):
    new_set = []
    closure_graph[node] = []
    for neighbour in original_graph[node]:
        neighbour_transitives = (closure_element(neighbour, original_graph, closure_graph))
        for member in neighbour_transitives:
            if member not in new_set:
                new_set.append(member)
        new_set.append(neighbour)
    for transitive_element in new_set:
        closure_graph[node].append(transitive_element)
    return new_set


def closure_element(node, original_graph, closure_graph):
    if node in closure_graph.keys():
        return closure_graph[node]
    else:
        return create_closure_set(node, original_graph, closure_graph)


def transitive_closure(original_graph, closure_graph):
    for key in original_graph.keys():
        closure_element(key, original_graph, closure_graph)


# Python_Sub_Graph = {'s0': [], 's1': [], 's2': ['s1'], 's3': ['s0', 's1'], 's4': [], 's5': ['s0'], 's6': ['s4'],
#                     's7': ['s0'], 's8': ['s1', 's2', 's3'], 's9': ['s1', 's2'], 's10': ['s2', 's6', 's8'],
#                     's11': ['s4', 's10'], 's12': ['s0', 's6', 's7', 's9'], 's13': ['s0', 's2', 's4', 's7'],
#                     's14': ['s0', 's4', 's11', 's13'], 's15': ['s1', 's6', 's12', 's14'],
#                     's16': ['s7', 's9', 's11', 's14', 's15'], 's17': ['s1', 's7', 's11', 's16'],
#                     's18': ['s2', 's3', 's5', 's6', 's7', 's17'], 's19': ['s0', 's1', 's6', 's13', 's15', 's16', 's18']}
#
# closureGraph = dict()
#
# transitive_closure(Python_Sub_Graph, closureGraph)
# print(closureGraph)
