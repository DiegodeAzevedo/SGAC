from z3 import *
import set_functions
import re

set_param(max_width=3000)
set_param(max_depth=5000000000000000000000000)
set_param(max_args=100000000000000)
set_param(max_lines=10000000000000)
set_param(max_indent=1000000000000)

s = Solver()  # Declaring the Z3 solver and storing it to the variable s.

'''
Starting to describe the SETS and PROPERTIES clauses fo the B machine.
'''

# Creating the Subject Graph
V_SUB = DeclareSort('Vertex_Subject')  # Declaring a type 'Vertex_Subject' (Vertex of the Subject Graph)
# Adding the Graph Nodes
s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17,\
s18, s19 = Consts('s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 '
                  's18 s19', V_SUB)  # Creating the nodes s0 - s19 to the Subject Graph
# Defining that the nodes are distinct (s0 != s1 != s2 != ... != s19)
s.add(Distinct(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19))


V_RES = DeclareSort('Vertex_Resource')  # Declaring a type 'Vertex_Resource' (Vertex of the Resource Graph)
r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,\
r18, r19 = Consts('r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17'
                  ' r18 r19', V_RES)  # Creating the nodes r0 - r19 to the Resource Graph
# Defining that the elements are distinct (r1 != r2 != r3 != ... != r19)
s.add(Distinct(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19))

Sub_Graph = Function('Subject_Graph', V_SUB, V_SUB, BoolSort())  # Declaring the Subject Graph
# Making a initialisation of the Graph
auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)
s.add(Sub_Graph(s2, s1), Sub_Graph(s3, s0), Sub_Graph(s3, s1), Sub_Graph(s5, s0),
      Sub_Graph(s6, s4), Sub_Graph(s7, s0), Sub_Graph(s8, s1), Sub_Graph(s8, s2),
      Sub_Graph(s8, s3), Sub_Graph(s9, s1), Sub_Graph(s9, s2), Sub_Graph(s10, s2),
      Sub_Graph(s10, s6), Sub_Graph(s10, s8), Sub_Graph(s11, s4), Sub_Graph(s11, s10),
      Sub_Graph(s12, s0), Sub_Graph(s12, s6), Sub_Graph(s12, s7), Sub_Graph(s12, s9),
      Sub_Graph(s13, s0), Sub_Graph(s13, s2), Sub_Graph(s13, s4), Sub_Graph(s13, s7),
      Sub_Graph(s14, s0), Sub_Graph(s14, s4), Sub_Graph(s14, s11), Sub_Graph(s14, s13),
      Sub_Graph(s15, s1), Sub_Graph(s15, s6), Sub_Graph(s15, s12), Sub_Graph(s15, s14),
      Sub_Graph(s16, s7), Sub_Graph(s16, s9), Sub_Graph(s16, s11), Sub_Graph(s16, s14),
      Sub_Graph(s16, s15), Sub_Graph(s17, s1), Sub_Graph(s17, s7), Sub_Graph(s17, s11),
      Sub_Graph(s17, s16), Sub_Graph(s18, s2), Sub_Graph(s18, s3), Sub_Graph(s18, s5),
      Sub_Graph(s18, s6), Sub_Graph(s18, s7), Sub_Graph(s18, s17), Sub_Graph(s19, s0),
      Sub_Graph(s19, s1), Sub_Graph(s19, s6), Sub_Graph(s19, s13), Sub_Graph(s19, s15),
      Sub_Graph(s19, s16), Sub_Graph(s19, s18))
s.add(ForAll([auxSub1, auxSub2], If(Or(And(auxSub1 == s2, auxSub2 == s1), And(auxSub1 == s3, auxSub2 == s0),
                                       And(auxSub1 == s3, auxSub2 == s1), And(auxSub1 == s5, auxSub2 == s0),
                                       And(auxSub1 == s6, auxSub2 == s4), And(auxSub1 == s7, auxSub2 == s0),
                                       And(auxSub1 == s8, auxSub2 == s1), And(auxSub1 == s8, auxSub2 == s2),
                                       And(auxSub1 == s8, auxSub2 == s3), And(auxSub1 == s9, auxSub2 == s1),
                                       And(auxSub1 == s9, auxSub2 == s2), And(auxSub1 == s10, auxSub2 == s2),
                                       And(auxSub1 == s10, auxSub2 == s6), And(auxSub1 == s10, auxSub2 == s8),
                                       And(auxSub1 == s11, auxSub2 == s4), And(auxSub1 == s11, auxSub2 == s10),
                                       And(auxSub1 == s12, auxSub2 == s0), And(auxSub1 == s12, auxSub2 == s6),
                                       And(auxSub1 == s12, auxSub2 == s7), And(auxSub1 == s12, auxSub2 == s9),
                                       And(auxSub1 == s13, auxSub2 == s0), And(auxSub1 == s13, auxSub2 == s2),
                                       And(auxSub1 == s13, auxSub2 == s4), And(auxSub1 == s13, auxSub2 == s7),
                                       And(auxSub1 == s14, auxSub2 == s0), And(auxSub1 == s14, auxSub2 == s4),
                                       And(auxSub1 == s14, auxSub2 == s11), And(auxSub1 == s14, auxSub2 == s13),
                                       And(auxSub1 == s15, auxSub2 == s1), And(auxSub1 == s15, auxSub2 == s6),
                                       And(auxSub1 == s15, auxSub2 == s12), And(auxSub1 == s15, auxSub2 == s14),
                                       And(auxSub1 == s16, auxSub2 == s7), And(auxSub1 == s16, auxSub2 == s9),
                                       And(auxSub1 == s16, auxSub2 == s11), And(auxSub1 == s16, auxSub2 == s14),
                                       And(auxSub1 == s16, auxSub2 == s15), And(auxSub1 == s17, auxSub2 == s1),
                                       And(auxSub1 == s17, auxSub2 == s7), And(auxSub1 == s17, auxSub2 == s11),
                                       And(auxSub1 == s17, auxSub2 == s16), And(auxSub1 == s18, auxSub2 == s2),
                                       And(auxSub1 == s18, auxSub2 == s3), And(auxSub1 == s18, auxSub2 == s5),
                                       And(auxSub1 == s18, auxSub2 == s6), And(auxSub1 == s18, auxSub2 == s7),
                                       And(auxSub1 == s18, auxSub2 == s17), And(auxSub1 == s19, auxSub2 == s0),
                                       And(auxSub1 == s19, auxSub2 == s1), And(auxSub1 == s19, auxSub2 == s6),
                                       And(auxSub1 == s19, auxSub2 == s13), And(auxSub1 == s19, auxSub2 == s15),
                                       And(auxSub1 == s19, auxSub2 == s16), And(auxSub1 == s19, auxSub2 == s18)),
                                    Sub_Graph(auxSub1, auxSub2) == True, Sub_Graph(auxSub1, auxSub2) == False)))
# Same graph of the Z3, but declared as a python dictionary.
Python_Sub_Graph = {s0: [], s1: [], s2: [s1], s3: [s0, s1], s4: [], s5: [s0], s6: [s4], s7: [s0], s8: [s1, s2, s3],
                    s9: [s1, s2], s10: [s2, s6, s8], s11: [s4, s10], s12: [s0, s6, s7, s9], s13: [s0, s2, s4, s7],
                    s14: [s0, s4, s11, s13], s15: [s1, s6, s12, s14], s16: [s7, s9, s11, s14, s15],
                    s17: [s1, s7, s11, s16], s18: [s2, s3, s5, s6, s7, s17], s19: [s0, s1, s6, s13, s15, s16, s18]}
# Auxiliary graph, used to storage the Subject_Closure_Graph as a python dictionary.
Python_Subject_Closure_Graph = dict()
# Creating the Transitive Closure Graph
set_functions.transitive_closure(Python_Sub_Graph, Python_Subject_Closure_Graph)
# Defining the transitive closure as a Z3 function
Subject_Closure_Graph = Function('Transitive_Closure_Graph', V_SUB, V_SUB, BoolSort())
auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)  # Constants to define the ForAll
expressionList1 = []  # List of expressions in the format Subject_Closure_Graph(x, y)
expressionList2 = []  # List of expressions in the format And(x == V_SUB.element, y == V_SUB.element)
for key in Python_Subject_Closure_Graph.keys():
    for node in Python_Subject_Closure_Graph[key]:
        expressionList1.append(Subject_Closure_Graph(key, node))
        expressionList2.append(And(auxSub1 == key, auxSub2 == node))

if expressionList1:  # If the expression list is not empty. The graph is not empty.
    for formula in expressionList1:
        s.add(formula)  # Adding the pairs to the solver
    s.add(ForAll([auxSub1, auxSub2], If(Or(expressionList2),
                                        Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                        # Making the remaining false.
                                        Subject_Closure_Graph(auxSub1, auxSub2) == False)))


Res_Graph = Function('Resources_Graph', V_RES, V_RES, BoolSort())  # Declaring the Resources Graph
# Making the initialisation of the Graph
auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
s.add(Res_Graph(r2, r1), Res_Graph(r4, r3), Res_Graph(r6, r1), Res_Graph(r6, r2), Res_Graph(r6, r5), Res_Graph(r7, r4),
      Res_Graph(r7, r6), Res_Graph(r8, r1), Res_Graph(r8, r4), Res_Graph(r8, r6), Res_Graph(r9, r0), Res_Graph(r9, r1),
      Res_Graph(r10, r1), Res_Graph(r10, r4), Res_Graph(r10, r6), Res_Graph(r10, r8), Res_Graph(r10, r9),
      Res_Graph(r11, r0), Res_Graph(r11, r5), Res_Graph(r11, r7), Res_Graph(r11, r8), Res_Graph(r12, r0),
      Res_Graph(r12, r1), Res_Graph(r12, r4), Res_Graph(r12, r10), Res_Graph(r12, r11), Res_Graph(r13, r1),
      Res_Graph(r13, r5), Res_Graph(r13, r6), Res_Graph(r13, r8), Res_Graph(r13, r11), Res_Graph(r13, r12),
      Res_Graph(r14, r4), Res_Graph(r14, r5), Res_Graph(r14, r6), Res_Graph(r14, r7), Res_Graph(r14, r10),
      Res_Graph(r15, r5), Res_Graph(r15, r9), Res_Graph(r15, r10), Res_Graph(r15, r12), Res_Graph(r15, r14),
      Res_Graph(r16, r8), Res_Graph(r16, r11), Res_Graph(r16, r14), Res_Graph(r17, r3), Res_Graph(r17, r12),
      Res_Graph(r17, r13), Res_Graph(r17, r16), Res_Graph(r18, r1), Res_Graph(r18, r4), Res_Graph(r18, r5),
      Res_Graph(r18, r10), Res_Graph(r18, r15), Res_Graph(r18, r17), Res_Graph(r19, r1), Res_Graph(r19, r6),
      Res_Graph(r19, r8), Res_Graph(r19, r14), Res_Graph(r19, r15), Res_Graph(r19, r16), Res_Graph(r19, r17),
      Res_Graph(r19, r18))
s.add(ForAll([auxRes1, auxRes2], If(Or(And(auxRes1 == r2, auxRes2 == r1), And(auxRes1 == r4, auxRes2 == r3),
                                       And(auxRes1 == r6, auxRes2 == r1), And(auxRes1 == r6, auxRes2 == r2),
                                       And(auxRes1 == r6, auxRes2 == r5), And(auxRes1 == r7, auxRes2 == r4),
                                       And(auxRes1 == r7, auxRes2 == r6), And(auxRes1 == r8, auxRes2 == r1),
                                       And(auxRes1 == r8, auxRes2 == r4), And(auxRes1 == r8, auxRes2 == r6),
                                       And(auxRes1 == r9, auxRes2 == r0), And(auxRes1 == r9, auxRes2 == r1),
                                       And(auxRes1 == r10, auxRes2 == r1), And(auxRes1 == r10, auxRes2 == r4),
                                       And(auxRes1 == r10, auxRes2 == r6), And(auxRes1 == r10, auxRes2 == r8),
                                       And(auxRes1 == r10, auxRes2 == r9), And(auxRes1 == r11, auxRes2 == r0),
                                       And(auxRes1 == r11, auxRes2 == r5), And(auxRes1 == r11, auxRes2 == r7),
                                       And(auxRes1 == r11, auxRes2 == r8), And(auxRes1 == r12, auxRes2 == r0),
                                       And(auxRes1 == r12, auxRes2 == r1), And(auxRes1 == r12, auxRes2 == r4),
                                       And(auxRes1 == r12, auxRes2 == r10), And(auxRes1 == r12, auxRes2 == r11),
                                       And(auxRes1 == r13, auxRes2 == r1), And(auxRes1 == r13, auxRes2 == r5),
                                       And(auxRes1 == r13, auxRes2 == r6), And(auxRes1 == r13, auxRes2 == r8),
                                       And(auxRes1 == r13, auxRes2 == r11), And(auxRes1 == r13, auxRes2 == r12),
                                       And(auxRes1 == r14, auxRes2 == r4), And(auxRes1 == r14, auxRes2 == r5),
                                       And(auxRes1 == r14, auxRes2 == r6), And(auxRes1 == r14, auxRes2 == r7),
                                       And(auxRes1 == r14, auxRes2 == r10), And(auxRes1 == r15, auxRes2 == r5),
                                       And(auxRes1 == r15, auxRes2 == r9), And(auxRes1 == r15, auxRes2 == r10),
                                       And(auxRes1 == r15, auxRes2 == r12), And(auxRes1 == r15, auxRes2 == r14),
                                       And(auxRes1 == r16, auxRes2 == r8), And(auxRes1 == r16, auxRes2 == r11),
                                       And(auxRes1 == r16, auxRes2 == r14), And(auxRes1 == r17, auxRes2 == r3),
                                       And(auxRes1 == r17, auxRes2 == r12), And(auxRes1 == r17, auxRes2 == r13),
                                       And(auxRes1 == r17, auxRes2 == r16), And(auxRes1 == r18, auxRes2 == r1),
                                       And(auxRes1 == r18, auxRes2 == r4), And(auxRes1 == r18, auxRes2 == r5),
                                       And(auxRes1 == r18, auxRes2 == r10), And(auxRes1 == r18, auxRes2 == r15),
                                       And(auxRes1 == r18, auxRes2 == r17), And(auxRes1 == r19, auxRes2 == r1),
                                       And(auxRes1 == r19, auxRes2 == r6), And(auxRes1 == r19, auxRes2 == r8),
                                       And(auxRes1 == r19, auxRes2 == r14), And(auxRes1 == r19, auxRes2 == r15),
                                       And(auxRes1 == r19, auxRes2 == r16), And(auxRes1 == r19, auxRes2 == r17),
                                       And(auxRes1 == r19, auxRes2 == r18)),
                                    Res_Graph(auxRes1, auxRes2) == True, Res_Graph(auxRes1, auxRes2) == False)))
# Same resource graph of the Z3, but declared as a python dictionary.
Python_Res_Graph = {r0: [], r1: [], r2: [r1], r3: [], r4: [r3], r5: [], r6: [r1, r2, r5], r7: [r4, r6],
                    r8: [r1, r4, r6], r9: [r0, r1], r10: [r1, r4, r6, r8, r9], r11: [r0, r5, r7, r8],
                    r12: [r0, r1, r4, r10, r11], r13: [r1, r5, r6, r8, r11, r12], r14: [r4, r5, r6, r7, r10],
                    r15: [r5, r9, r10, r12, r14], r16: [r8, r11, r14], r17: [r3, r12, r13, r16],
                    r18: [r1, r4, r5, r10, r15, r17], r19: [r1, r6, r8, r14, r15, r16, r17, r18]}
# Auxiliary graph, used to storage the Subject_Closure_Graph as a python dictionary.
Python_Resource_Closure_Graph = dict()
# Creating the Transitive Closure Graph
set_functions.transitive_closure(Python_Res_Graph, Python_Resource_Closure_Graph)
# Defining the transitive closure as a Z3 function
Resource_Closure_Graph = Function('Transitive_Closure_Graph', V_RES, V_RES, BoolSort())
auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)  # Constants to define the ForAll
expressionList1 = []  # List of expressions in the format Subject_Closure_Graph(x, y)
expressionList2 = []  # List of expressions in the format And(x == V_SUB.element, y == V_SUB.element)
for key in Python_Resource_Closure_Graph.keys():
    for node in Python_Resource_Closure_Graph[key]:
        expressionList1.append(Resource_Closure_Graph(key, node))
        expressionList2.append(And(auxRes1 == key, auxRes2 == node))

if expressionList1:  # If the expression list is not empty. The graph is not empty.
    for formula in expressionList1:
        s.add(formula)  # Adding the pairs to the solver
    s.add(ForAll([auxRes1, auxRes2], If(Or(expressionList2),
                            Resource_Closure_Graph(auxRes1, auxRes2) == True,
                            Resource_Closure_Graph(auxRes1, auxRes2) == False)))  # Making the remaining false.

# Adding the REQUEST_T constant as a z3 relation between (V_SUB-dom(e_sub)) * (V_RES-dom(e_res))
REQUEST_T = Function('REQUEST_T', V_SUB, V_RES, BoolSort())
notDomainSUB = Function('notDomainSub', V_SUB, BoolSort())
notDomainRES = Function('notDomainRES', V_RES, BoolSort())
# Auxiliary variables to the declaration of the predicate of REQUEST_T.
auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)
# Auxiliary variables to the declaration of the predicate of REQUEST_T.
auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
# Formulas to describe REQUEST_T
s.add(ForAll(auxSub1, If(Not(Exists(auxSub2, Sub_Graph(auxSub1, auxSub2))),
                         notDomainSUB(auxSub1), notDomainSUB(auxSub1) == False)))
s.add(ForAll(auxRes1, If(Not(Exists(auxRes2, Res_Graph(auxRes1, auxRes2))),
                         notDomainRES(auxRes1), notDomainRES(auxRes1) == False)))
s.add(ForAll([auxSub1, auxRes1], Implies(And(notDomainSUB(auxSub1),
                                             notDomainRES(auxRes1)),
                                         REQUEST_T(auxSub1, auxRes1))))
s.add(Implies(notDomainRES(auxRes1), And(Not(Exists(auxRes2, Res_Graph(auxRes1, auxRes2))
                                             ),
                                         Or(auxRes1 == r0, auxRes1 == r1, auxRes1 == r2, auxRes1 == r3,
                                            auxRes1 == r4, auxRes1 == r5, auxRes1 == r6, auxRes1 == r7,
                                            auxRes1 == r8, auxRes1 == r9, auxRes1 == r10, auxRes1 == r11,
                                            auxRes1 == r12, auxRes1 == r13, auxRes1 == r14, auxRes1 == r15,
                                            auxRes1 == r16, auxRes1 == r17, auxRes1 == r18, auxRes1 == r19)
                                         )
              )
      )
s.add(Implies(notDomainSUB(auxSub1), And(Not(Exists(auxSub2, Sub_Graph(auxSub1, auxSub2))),
                                         Or(auxSub1 == s0, auxSub1 == s1, auxSub1 == s2, auxSub1 == s3, auxSub1 == s4,
                                            auxSub1 == s5, auxSub1 == s6, auxSub1 == s7, auxSub1 == s8, auxSub1 == s9,
                                            auxSub1 == s10, auxSub1 == s11, auxSub1 == s12, auxSub1 == s13,
                                            auxSub1 == s14, auxSub1 == s15, auxSub1 == s16, auxSub1 == s17,
                                            auxSub1 == s18, auxSub1 == s19)
                                         )
              )
      )
s.add(Implies(REQUEST_T(auxSub1, auxRes1), And(notDomainSUB(auxSub1),
                                               notDomainRES(auxRes1))))
# Making REQUEST_T only valid to the described Subjects and Resources
s.add(Not(Exists([auxSub1, auxRes1], Or(And(auxSub1 != s0, auxSub1 != s1, auxSub1 != s2, auxSub1 != s3, auxSub1 != s4,
                                             auxSub1 != s5, auxSub1 != s6, auxSub1 != s7, auxSub1 != s8, auxSub1 != s9,
                                             auxSub1 != s10, auxSub1 != s11, auxSub1 != s12, auxSub1 != s13,
                                             auxSub1 != s14, auxSub1 != s15, auxSub1 != s16, auxSub1 != s17,
                                             auxSub1 != s18, auxSub1 != s19),
                                         And(auxRes1 != r0, auxRes1 != r1, auxRes1 != r2, auxRes1 != r3, auxRes1 != r4,
                                             auxRes1 != r5, auxRes1 != r6, auxRes1 != r7, auxRes1 != r8, auxRes1 != r9,
                                             auxRes1 != r10, auxRes1 != r11, auxRes1 != r12, auxRes1 != r13,
                                             auxRes1 != r14, auxRes1 != r15, auxRes1 != r16, auxRes1 != r17,
                                             auxRes1 != r18, auxRes1 != r19)))))

MODALITY = DeclareSort('ModalityType')  # Creation of modality type.
permission, prohibition = Consts('permission prohibition', MODALITY)  # Creating modality elements.
s.add(Distinct(permission, prohibition))

CONTEXT = DeclareSort('Context')  # Creation of a context.
c0, c1, c2 = Consts('c0 c1 c2', CONTEXT)  # Going to change this later to predicates.
s.add(Distinct(c0, c1, c2))

rules = DeclareSort('rules')  # Creation of a rule type RULE_T in the B machine.
rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38,\
rule39 = Consts('rule30 rule31 rule32 rule33 rule34 rule35 rule36 rule37 rule38 rule39', rules)
s.add(Distinct(rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39))
# Not letting the value of the rules escape
# Auxiliary variables to the declaration of the predicate above.
auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
s.add(Not(Exists([auxRule1, auxRule2],
                 And(And(auxRule2 != rule30, auxRule2 != rule31, auxRule2 != rule32, auxRule2 != rule33,
                         auxRule2 != rule34, auxRule2 != rule35, auxRule2 != rule36, auxRule2 != rule37,
                         auxRule2 != rule38, auxRule2 != rule39),
                     And(auxRule1 != rule30, auxRule1 != rule31, auxRule1 != rule32, auxRule1 != rule33,
                         auxRule1 != rule34, auxRule1 != rule35, auxRule1 != rule36, auxRule1 != rule37,
                         auxRule1 != rule38, auxRule1 != rule39)))))


# Creation of several graphs as a z3 relation. Used to describe a rule parameters.
rule_subject = Function('rule_subject', rules, V_SUB, BoolSort())
rule_resource = Function('rule_resource', rules, V_RES, BoolSort())
rule_modality = Function('rule_modality', rules, MODALITY, BoolSort())
rule_priority = Function('rule_priority', rules, IntSort(), BoolSort())
rule_condition = Function('rule_condition', rules, CONTEXT, BoolSort())

# Adding the subject for each specific rule.
s.add(rule_subject(rule30, s19), rule_subject(rule31, s7), rule_subject(rule32, s11), rule_subject(rule33, s13),
      rule_subject(rule34, s3), rule_subject(rule35, s7), rule_subject(rule36, s13), rule_subject(rule37, s14),
      rule_subject(rule38, s8), rule_subject(rule39, s0))
auxRule1 = Const('auxRule1', rules)
auxSub1 = Const('auxSub1', V_SUB)
s.add(ForAll([auxRule1, auxSub1],
             # If any of this options
             If(Or(And(auxRule1 == rule30, auxSub1 == s19), And(auxRule1 == rule31, auxSub1 == s7),
                   And(auxRule1 == rule32, auxSub1 == s11), And(auxRule1 == rule33, auxSub1 == s13),
                   And(auxRule1 == rule34, auxSub1 == s3), And(auxRule1 == rule35, auxSub1 == s7),
                   And(auxRule1 == rule36, auxSub1 == s13), And(auxRule1 == rule37, auxSub1 == s14),
                   And(auxRule1 == rule38, auxSub1 == s8), And(auxRule1 == rule39, auxSub1 == s0)),
                rule_subject(auxRule1, auxSub1) == True,  # Then True
                rule_subject(auxRule1, auxSub1) == False)))  # Else -> False


# Adding the resource for each specific rule.
s.add(rule_resource(rule30, r17), rule_resource(rule31, r0), rule_resource(rule32, r14), rule_resource(rule33, r6),
      rule_resource(rule34, r8), rule_resource(rule35, r11), rule_resource(rule36, r6), rule_resource(rule37, r4),
      rule_resource(rule38, r15), rule_resource(rule39, r14))
auxRes1 = Const('auxRes1', V_RES)
s.add(ForAll([auxRule1, auxRes1],
             # If any of this options
             If(Or(And(auxRule1 == rule30, auxRes1 == r17), And(auxRule1 == rule31, auxRes1 == r0),
                   And(auxRule1 == rule32, auxRes1 == r14), And(auxRule1 == rule33, auxRes1 == r6),
                   And(auxRule1 == rule34, auxRes1 == r8), And(auxRule1 == rule35, auxRes1 == r11),
                   And(auxRule1 == rule36, auxRes1 == r6), And(auxRule1 == rule37, auxRes1 == r4),
                   And(auxRule1 == rule38, auxRes1 == r15), And(auxRule1 == rule39, auxRes1 == r14)),
                rule_resource(auxRule1, auxRes1) == True,  # Then True
                rule_resource(auxRule1, auxRes1) == False)))  # Else -> False

# Adding the modality for each specific rule.
s.add(rule_modality(rule30, prohibition), rule_modality(rule31, permission), rule_modality(rule32, permission),
      rule_modality(rule33, permission), rule_modality(rule34, prohibition), rule_modality(rule35, prohibition),
      rule_modality(rule36, permission), rule_modality(rule37, prohibition), rule_modality(rule38, prohibition),
      rule_modality(rule39, permission))
auxModality = Const('auxModality', MODALITY)
s.add(ForAll([auxRule1, auxModality], If(Or(And(auxRule1 == rule30, auxModality == prohibition),
                                            And(auxRule1 == rule31, auxModality == permission),
                                            And(auxRule1 == rule32, auxModality == permission),
                                            And(auxRule1 == rule33, auxModality == permission),
                                            And(auxRule1 == rule34, auxModality == prohibition),
                                            And(auxRule1 == rule35, auxModality == prohibition),
                                            And(auxRule1 == rule36, auxModality == permission),
                                            And(auxRule1 == rule37, auxModality == prohibition),
                                            And(auxRule1 == rule38, auxModality == prohibition),
                                            And(auxRule1 == rule39, auxModality == permission)),  # If it is this
                                         rule_modality(auxRule1, auxModality) == True,  # Then True
                                         rule_modality(auxRule1, auxModality) == False)))  # Else -> False

# Adding the priority for each specific rule.
s.add(rule_priority(rule30, 1), rule_priority(rule31, 3), rule_priority(rule32, 4), rule_priority(rule33, 1),
      rule_priority(rule34, 3), rule_priority(rule35, 0), rule_priority(rule36, 1), rule_priority(rule37, 1),
      rule_priority(rule38, 0), rule_priority(rule39, 1))
auxInt = Const('auxInt', IntSort())
s.add(ForAll([auxRule1, auxInt], If(Or(And(auxRule1 == rule30, auxInt == 1), And(auxRule1 == rule31, auxInt == 3),
                                       And(auxRule1 == rule32, auxInt == 4), And(auxRule1 == rule33, auxInt == 1),
                                       And(auxRule1 == rule34, auxInt == 3), And(auxRule1 == rule35, auxInt == 0),
                                       And(auxRule1 == rule36, auxInt == 1), And(auxRule1 == rule37, auxInt == 1),
                                       And(auxRule1 == rule38, auxInt == 0), And(auxRule1 == rule39, auxInt == 1)),
                                    # If it is this
                                    rule_priority(auxRule1, auxInt) == True,  # Then True
                                    rule_priority(auxRule1, auxInt) == False)))  # Else -> False

# Adding the condition for each specific rule.
s.add(rule_condition(rule30, c2), rule_condition(rule30, c0), rule_condition(rule31, c0), rule_condition(rule31, c2),
      rule_condition(rule32, c0), rule_condition(rule33, c1), rule_condition(rule33, c0), rule_condition(rule34, c2),
      rule_condition(rule35, c0), rule_condition(rule35, c2), rule_condition(rule36, c1), rule_condition(rule37, c2),
      rule_condition(rule38, c2), rule_condition(rule38, c0), rule_condition(rule39, c0), rule_condition(rule39, c1))
auxCon = Const('auxCon', CONTEXT)
s.add(ForAll([auxRule1, auxCon],
             # If any of this options
             If(Or(And(auxRule1 == rule30, auxCon == c2), And(auxRule1 == rule30, auxCon == c0),
                   And(auxRule1 == rule31, auxCon == c0), And(auxRule1 == rule31, auxCon == c2),
                   And(auxRule1 == rule32, auxCon == c0), And(auxRule1 == rule33, auxCon == c1),
                   And(auxRule1 == rule33, auxCon == c0), And(auxRule1 == rule34, auxCon == c2),
                   And(auxRule1 == rule35, auxCon == c0), And(auxRule1 == rule35, auxCon == c2),
                   And(auxRule1 == rule36, auxCon == c1), And(auxRule1 == rule37, auxCon == c2),
                   And(auxRule1 == rule38, auxCon == c2), And(auxRule1 == rule38, auxCon == c0),
                   And(auxRule1 == rule39, auxCon == c0), And(auxRule1 == rule39, auxCon == c1)),
                rule_condition(auxRule1, auxCon) == True,  # Then True
                rule_condition(auxRule1, auxCon) == False)))  # Else -> False

# Adding the lessSpecific constant as a z3 relation between rules.
lessSpecific = Function('lessSpecific', rules, rules, BoolSort())
# Auxiliary variables to the declaration of the predicate of lessSpecific.
auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
# Auxiliary variables to the declaration of the predicate of lessSpecific.
auxInt1, auxInt2 = Consts('auxInt1 auxInt2', IntSort())
# Auxiliary variables to the declaration of the predicate of lessSpecific.
auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)
s.add(Implies(lessSpecific(auxRule1, auxRule2),
              And(rule_priority(auxRule1, auxInt1), rule_priority(auxRule2, auxInt2),
                  rule_subject(auxRule1, auxSub1), rule_subject(auxRule2, auxSub2),
                  auxRule1 != auxRule2,
                  Or(auxInt1 > auxInt2, And(auxInt1 == auxInt2, Subject_Closure_Graph(auxSub1, auxSub2)))
                  )
              )

      )
s.add(ForAll([auxRule1, auxRule2, auxInt1, auxInt2, auxSub1, auxSub2],
             Implies(And(rule_priority(auxRule1, auxInt1), rule_priority(auxRule2, auxInt2),
                         rule_subject(auxRule1, auxSub1), rule_subject(auxRule2, auxSub2),
                         auxRule1 != auxRule2,
                         Or(auxInt1 > auxInt2, And(auxInt1 == auxInt2,
                                                   Subject_Closure_Graph(auxSub1, auxSub2)))),
                     lessSpecific(auxRule1, auxRule2))))  # Formula that fits lessSpecific.

'''
Starting to describe the VARIABLES and INVARIANT clauses from the B machine.
'''
conRule = Function('conRule', CONTEXT, rules, BoolSort())  # Creating of the variable ConRule
auxCon = Const('auxCon', CONTEXT)
auxRule1 = Const('auxRule1', rules)
s.add(ForAll([auxCon, auxRule1], Implies(rule_condition(auxRule1, auxCon), conRule(auxCon, auxRule1))))
s.add(Implies(conRule(auxCon, auxRule1), rule_condition(auxRule1, auxCon)))

applicable = Function('applicable', V_SUB, V_RES, rules, BoolSort())  # Declaring VARIABLE applicable
auxRule1 = Const('auxRule1', rules)
auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)
# Defining the applicable variable
s.add(Implies(applicable(auxSub1, auxRes1, auxRule1),
              And(Or(rule_subject(auxRule1, auxSub1),
                     And(Subject_Closure_Graph(auxSub2, auxSub1),
                         rule_subject(auxRule1, auxSub2))),
                  Or(rule_resource(auxRule1, auxRes1),
                     And(rule_resource(auxRule1, auxRes2),
                         Resource_Closure_Graph(auxRes2, auxRes1))),
                  REQUEST_T(auxSub1, auxRes1))))
s.add(ForAll([auxRes1, auxSub2, auxRule1, auxRes2, auxSub1], Implies(And(Or(rule_subject(auxRule1, auxSub1),
                                                                           And(rule_subject(auxRule1, auxSub2),
                                                                               Subject_Closure_Graph(auxSub2,
                                                                                                     auxSub1))),
                                                                        Or(rule_resource(auxRule1, auxRes1),
                                                                           And(rule_resource(auxRule1, auxRes2),
                                                                               Resource_Closure_Graph(auxRes2, auxRes1))),
                                                                        REQUEST_T(auxSub1, auxRes1)),
                                                                    applicable(auxSub1, auxRes1, auxRule1))))


maxElem = Function('maxElem', V_SUB, V_RES, rules, BoolSort())
auxRes1 = Const('auxRes1', V_RES)
auxSub1 = Const('auxSub1', V_SUB)
auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
# s.add(ForAll([auxSub1, auxRes1, auxRule1],
#              Implies(And(applicable(auxSub1, auxRes1, auxRule1),
#                          Not(Exists(auxRule2, And(applicable(auxSub1, auxRes1, auxRule2),
#                                                   lessSpecific(auxRule1, auxRule2)
#                                                   )
#                                     )
#                              ),
#                          REQUEST_T(auxSub1, auxRes1)
#                          ),
#                      maxElem(auxSub1, auxRes1, auxRule1))
#              )
#       )
s.add(maxElem(s0, r0, rule35), maxElem(s0, r0, rule38),
      maxElem(s0, r1, rule35), maxElem(s0, r1, rule38),
      maxElem(s0, r3, rule35), maxElem(s0, r3, rule38),
      maxElem(s0, r5, rule35), maxElem(s0, r5, rule38),
      maxElem(s1, r0, rule38),
      maxElem(s1, r1, rule38),
      maxElem(s1, r3, rule38),
      maxElem(s1, r5, rule38),
      maxElem(s4, r0, rule30),
      maxElem(s4, r1, rule33), maxElem(s4, r1, rule36),
      maxElem(s4, r3, rule37),
      maxElem(s4, r5, rule33), maxElem(s4, r5, rule36)
      )
s.add(ForAll([auxSub1, auxRes1, auxRule1],
             If(Or(And(auxSub1 == s0, auxRes1 == r0, auxRule1 == rule35),
                   And(auxSub1 == s0, auxRes1 == r0, auxRule1 == rule38),
                   And(auxSub1 == s0, auxRes1 == r1, auxRule1 == rule35),
                   And(auxSub1 == s0, auxRes1 == r1, auxRule1 == rule38),
                   And(auxSub1 == s0, auxRes1 == r3, auxRule1 == rule35),
                   And(auxSub1 == s0, auxRes1 == r3, auxRule1 == rule38),
                   And(auxSub1 == s0, auxRes1 == r5, auxRule1 == rule35),
                   And(auxSub1 == s0, auxRes1 == r5, auxRule1 == rule38),
                   And(auxSub1 == s1, auxRes1 == r0, auxRule1 == rule38),
                   And(auxSub1 == s1, auxRes1 == r1, auxRule1 == rule38),
                   And(auxSub1 == s1, auxRes1 == r3, auxRule1 == rule38),
                   And(auxSub1 == s1, auxRes1 == r5, auxRule1 == rule38),
                   And(auxSub1 == s4, auxRes1 == r0, auxRule1 == rule30),
                   And(auxSub1 == s4, auxRes1 == r1, auxRule1 == rule33),
                   And(auxSub1 == s4, auxRes1 == r1, auxRule1 == rule36),
                   And(auxSub1 == s4, auxRes1 == r3, auxRule1 == rule37),
                   And(auxSub1 == s4, auxRes1 == r5, auxRule1 == rule33),
                   And(auxSub1 == s4, auxRes1 == r5, auxRule1 == rule36)),
                maxElem(auxSub1, auxRes1, auxRule1),
                Not(maxElem(auxSub1, auxRes1, auxRule1)))))


# isPrecededBy = Function('isPrecededBy', V_SUB, V_RES, rules, rules, BoolSort())
# auxRule1, auxRule2, auxRule3 = Consts('auxRule1 auxRule2 auxRule3', rules)
# auxRes1 = Const('auxRes1', V_RES)
# auxSub1 = Const('auxSub1', V_SUB)
# s.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],  # xx == (auxSub1, auxRes1)
#              Implies(And(applicable(auxSub1, auxRes1, auxRule1),  # auxRule1 == yy, yy : applicable(xx)
#                          applicable(auxSub1, auxRes1, auxRule2),  # auxRule2 == zz, zz : applicable(xx)
#                          auxRule1 != auxRule2,  # yy != zz
#                          Or(lessSpecific(auxRule1, auxRule2),  # yy|->zz : lessSpecific OR
#                             And(applicable(auxSub1, auxRes1, auxRule1),  # yy <: maxElem(xx)
#                                 Not(Exists(auxRule3, And(applicable(auxSub1, auxRes1, auxRule3),
#                                                          auxRule3 != auxRule1,
#                                                          lessSpecific(auxRule1, auxRule3)))),
#                                 applicable(auxSub1, auxRes1, auxRule1),  # zz <: maxElem(xx)
#                                 Not(Exists(auxRule3, And(applicable(auxSub1, auxRes1, auxRule3),
#                                                          auxRule3 != auxRule2,
#                                                          lessSpecific(auxRule2, auxRule3)))),
#                                 rule_modality(auxRule1, permission),  # rules(yy))'mo = per
#                                 rule_modality(auxRule2, prohibition)  # rules(zz))'mo = pro
#                                 )
#                             )
#                          ), isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)
#                      )
#              )
#       )


isPrecededBy = Function('isPrecededBy', V_SUB, V_RES, rules, rules, BoolSort())
auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
auxRes1 = Const('auxRes1', V_RES)
auxSub1 = Const('auxSub1', V_SUB)
s.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],
             Implies(And(REQUEST_T(auxSub1, auxRes1),  # xx == (auxSub1, auxRes1) == REQUEST_T
                         applicable(auxSub1, auxRes1, auxRule1),  # auxRule1 == yy, yy : applicable(xx)
                         applicable(auxSub1, auxRes1, auxRule2),  # auxRule2 == zz, zz : applicable(xx)
                         auxRule1 != auxRule2,  # yy != zz
                         Or(lessSpecific(auxRule1, auxRule2),  # yy|->zz : lessSpecific OR
                            And(maxElem(auxSub1, auxRes1, auxRule1),
                                maxElem(auxSub1, auxRes1, auxRule2),
                                rule_modality(auxRule1, permission),  # rules(yy))'mo = per
                                rule_modality(auxRule2, prohibition)  # rules(zz))'mo = pro
                                )
                            )
                         ), isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)
                     )
             )
      )
s.add(Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
              And(REQUEST_T(auxSub1, auxRes1),  # xx == (auxSub1, auxRes1) == REQUEST_T
                  applicable(auxSub1, auxRes1, auxRule1),  # auxRule1 == yy, yy : applicable(xx)
                  applicable(auxSub1, auxRes1, auxRule2),  # auxRule2 == zz, zz : applicable(xx)
                  auxRule1 != auxRule2,  # yy != zz
                  Or(lessSpecific(auxRule1, auxRule2),  # yy|->zz : lessSpecific OR
                     And(maxElem(auxSub1, auxRes1, auxRule1),
                         maxElem(auxSub1, auxRes1, auxRule2),
                         rule_modality(auxRule1, permission),  # rules(yy))'mo = per
                         rule_modality(auxRule2, prohibition)  # rules(zz))'mo = pro
                         )
                     )
                  )
              )
      )


# notPrecededInTheSameContext = Function("notPrecededInTheSameContext", CONTEXT, rules, rules, BoolSort())
# auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
# auxRes1 = Const('auxRes1', V_RES)
# auxSub1 = Const('auxSub1', V_SUB)
# auxCon = Const('auxCon', CONTEXT)
# s.add(Implies(notPrecededInTheSameContext(auxCon, auxRule1, auxRule2),
#               ForAll(auxRule2, Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
#                                        Not(conRule(auxCon, auxRule2)))
#                      )
#               )
#       )
# s.add(ForAll([auxCon, auxRule1, auxRule2],


# ruleSucc = Function('ruleSucc', V_SUB, V_RES, rules, BoolSort())
# auxRes1 = Const('auxRes1', V_RES)
# auxSub1 = Const('auxSub1', V_SUB)
# auxRule1, auxRule2, auxRule3 = Consts('auxRule1 auxRule2 auxRule3', rules)
# s.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],
#              Implies(And(applicable(auxSub1, auxRes1, auxRule1),
#                          applicable(auxSub1, auxRes1, auxRule2),
#                          REQUEST_T(auxSub1, auxRes1),
#                          isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
#                          Not(Exists(auxRule3,
#                                     And(applicable(auxSub1, auxRes1, auxRule3),
#                                         isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule3),
#                                         isPrecededBy(auxSub1, auxRes1, auxRule3, auxRule2),
#                                         auxRule1 != auxRule3,
#                                         auxRule2 != auxRule3)
#                                     )
#                              )
#                          ),
#                      ruleSucc(auxSub1, auxRes1, auxRule1, auxRule2)
#                      )
#              )
#       )


# pseudoSink = Function('pseudoSink', V_SUB, V_RES, CONTEXT, rules, BoolSort())
# auxRes1 = Const('auxRes1', V_RES)
# auxSub1 = Const('auxSub1', V_SUB)
# auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
# auxCon = Const('auxCon', CONTEXT)
# s.add(ForAll([auxSub1, auxRes1, auxCon, auxRule1],
#              If(And(REQUEST_T(auxSub1, auxRes1),
#                     applicable(auxSub1, auxRes1, auxRule1),
#                     conRule(auxCon, auxRule1),
#                     Not(Exists(auxRule2,
#                                And(applicable(auxSub1, auxRes1, auxRule2),
#                                    conRule(auxCon, auxRule2),
#                                    isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2))))),
#                 pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
#                 Not(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1))
#                 )
#              )
#       )
# s.add(Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
#               And(REQUEST_T(auxSub1, auxRes1),
#                   applicable(auxSub1, auxRes1, auxRule1),
#                   conRule(auxCon, auxRule1),
#                   ForAll(auxRule2,
#                          Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
#                                  Not(conRule(auxCon, auxRule2)
#                                      )
#                                  )
#                          )
#                   )
#               )
#       )
# s.add(ForAll([auxSub1, auxRes1, auxRule1, auxCon],
#              Implies(And(REQUEST_T(auxSub1, auxRes1),
#                          applicable(auxSub1, auxRes1, auxRule1),
#                          conRule(auxCon, auxRule1),
#                          ForAll(auxRule2,
#                                 Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
#                                         Not(conRule(auxCon, auxRule2)
#                                             )
#                                         )
#                                 )
#                          ),
#                      pseudoSink(auxSub1, auxRes1, auxCon, auxRule1)
#                      )
#              )
#       )


# s.add(ForAll([auxSub1, auxRes1, auxRule1, auxCon, auxRule2],
#              Implies(And(REQUEST_T(auxSub1, auxRes1),
#                          applicable(auxSub1, auxRes1, auxRule1),
#                          conRule(auxCon, auxRule1),
#                          Not(notInConRule_PseudoSink(auxCon, auxRule2))
#                          ),
#                      pseudoSink(auxSub1, auxRes1, auxCon, auxRule1)
#                      )
#              )
#       )


# s.add(ForAll([auxSub1, auxRes1, auxRule1, auxCon],
#              Implies(And(REQUEST_T(auxSub1, auxRes1),
#                          applicable(auxSub1, auxRes1, auxRule1),
#                          conRule(auxCon, auxRule1),
#                          If(ForAll(auxRule2, isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)),
#                             Not(conRule(auxCon, auxRule2)),
#                             conRule(auxCon, auxRule2))),
#                      pseudoSink(auxSub1, auxRes1, auxCon, auxRule1)
#                      )
#              )
#       )


# Declaring the four properties
# accessibility = Function('Accessibility', V_SUB, V_RES, CONTEXT, BoolSort())
# auxRes1 = Const('auxRes1', V_RES)
# auxSub1 = Const('auxSub1', V_SUB)
# auxRule1 = Const('auxRule1', rules)
# auxCon = Const('auxCon', CONTEXT)
# s.add(ForAll([auxSub1, auxRes1, auxCon],
#              And(REQUEST_T(auxSub1, auxRes1),
#                  Implies(And(ForAll(auxRule1, Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
#                                                       rule_modality(auxRule1, permission)
#                                                       )
#                                     )
#                              # , Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon, auxRule1)))
#                              ),
#                          accessibility(auxSub1, auxRes1, auxCon)
#                          )
#                  )
#              )
#       )

# hiddenDocument = Function('HiddenDocument', V_RES, auxCon, BoolSort())
# auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
# auxSub1 = Const('auxSub1', V_SUB)
# auxCon = Const('auxCon', CONTEXT)
# s.add(ForAll(auxRes1, auxCon, Implies(And(notDomainRES(auxRes1),
#                                           ForAll([auxSub1, auxRes2],
#                                                  Implies(And(REQUEST_T(auxSub1, auxRes2),
#                                                              auxRes2 == auxRes1
#                                                      # MISSING  prj2(V_SUB,V_RES)(req)=hdoc
#                                                              ),
#                                                          Not(accessibility(auxSub1, auxRes2, auxCon))
#                                                          )
#                                                  )
#                                           ),
#                                       hiddenDocument(auxRes1, auxCon)
#                                       )
#              )
#       )


# gratingContext = Function('gratingContext', V_SUB, V_RES, CONTEXT, BoolSort())

print(s.check())
if s.check() == sat:
    print(s.model()[Sub_Graph])
    print(s.model()[lessSpecific])
    print(s.model()[applicable])
    print(s.model()[isPrecededBy])
    # print(s.model()[pseudoSink])

    f = open("model.txt", "w+")
    for variable in s.model():
        f.write(str(variable)), f.write("="), f.write(str(s.model()[variable])), f.write("\n")
    f.close()

    dictOfSubstitutions = dict()
    chosenVariables = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
                       r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
                       rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39, c0, c1, c2,
                       permission, prohibition]

    # Rewriting the variables
    for variable in chosenVariables:
        with open("model.txt") as f:
            for line in f:
                matches = re.finditer(r""+str(variable)+"=", line)
                for matchNum, match in enumerate(matches):
                    dictOfSubstitutions[variable] = line[match.end():len(line)-1:]
        f.close()
    with open("model.txt", 'r') as f:
        modelContent = f.read()
    f.close()
    for key in dictOfSubstitutions.keys():
        modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0, re.MULTILINE)
    # Erasing the k!#### and replacing for the variables
    modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
    # Erasing k!#### variables
    modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
    # Erasing weird syntax from the solver (If(Var(0) == ...)
    modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "", modelContent)
    modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
    f = open("model.txt", "w+")
    f.write(modelContent)
    f.close()



