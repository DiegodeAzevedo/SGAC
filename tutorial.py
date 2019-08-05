from z3 import *
import set_functions

set_param(max_width=150)

s = Solver()

# Creating the Subject Graph
V_SUB = DeclareSort('Vertex_Subject')  # Declaring a type 'Vertex_Subject' (Vertex of the Subject Graph)
# Adding the Graph Nodes
s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17,\
s18, s19 = Consts('s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 '
                  's18 s19', V_SUB)  # Creating the nodes s0 - s19 to the Subject Graph
# Defining that the nodes are distinct (s0 != s1 != s2 != ... != s19)
s.add(Distinct(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19))

Sub_Graph = Function('Subject_Graph', V_SUB, V_SUB, BoolSort())  # Declaring the Subject Graph
# Making a initialisation of the Graph
x, y = Consts('x y', V_SUB)
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
s.add(ForAll([x, y], If(Or(And(x == s2, y == s1), And(x == s3, y == s0), And(x == s3, y == s1), And(x == s5, y == s0),
                        And(x == s6, y == s4), And(x == s7, y == s0), And(x == s8, y == s1), And(x == s8, y == s2),
                        And(x == s8, y == s3), And(x == s9, y == s1), And(x == s9, y == s2), And(x == s10, y == s2),
                        And(x == s10, y == s6), And(x == s10, y == s8), And(x == s11, y == s4), And(x == s11, y == s10),
                        And(x == s12, y == s0), And(x == s12, y == s6), And(x == s12, y == s7), And(x == s12, y == s9),
                        And(x == s13, y == s0), And(x == s13, y == s2), And(x == s13, y == s4), And(x == s13, y == s7),
                        And(x == s14, y == s0), And(x == s14, y == s4), And(x == s14, y == s11),
                        And(x == s14, y == s13), And(x == s15, y == s1), And(x == s15, y == s6),
                        And(x == s15, y == s12), And(x == s15, y == s14), And(x == s16, y == s7),
                        And(x == s16, y == s9), And(x == s16, y == s11), And(x == s16, y == s14),
                        And(x == s16, y == s15), And(x == s17, y == s1), And(x == s17, y == s7),
                        And(x == s17, y == s11), And(x == s17, y == s16), And(x == s18, y == s2),
                        And(x == s18, y == s3), And(x == s18, y == s5), And(x == s18, y == s6), And(x == s18, y == s7),
                        And(x == s18, y == s17), And(x == s19, y == s0), And(x == s19, y == s1), And(x == s19, y == s6),
                        And(x == s19, y == s13), And(x == s19, y == s15), And(x == s19, y == s16),
                        And(x == s19, y == s18)), Sub_Graph(x, y) == True, Sub_Graph(x, y) == False)))
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
x, y = Consts('x y', V_SUB)  # Constants to define the ForAll
expressionList1 = []  # List of expressions in the format Subject_Closure_Graph(x, y)
expressionList2 = []  # List of expressions in the format And(x == V_SUB.element, y == V_SUB.element)
for key in Python_Subject_Closure_Graph.keys():
    for node in Python_Subject_Closure_Graph[key]:
        expressionList1.append(Subject_Closure_Graph(key, node))
        expressionList2.append(And(x == key, y == node))

if expressionList1:  # If the expression list is not empty. The graph is not empty.
    for formula in expressionList1:
        s.add(formula)  # Adding the pairs to the solver
    s.add(ForAll([x, y], If(Or(expressionList2),
                            Subject_Closure_Graph(x, y) == True,
                            Subject_Closure_Graph(x, y) == False)))  # Making the remaining false.


V_RES = DeclareSort('Vertex_Resource')  # Declaring a type 'Vertex_Resource' (Vertex of the Resource Graph)
r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,\
r18, r19 = Consts('r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17'
                  ' r18 r19', V_RES)  # Creating the nodes r0 - r19 to the Resource Graph
# Defining that the elements are distinct (r1 != r2 != r3 != ... != r19)
s.add(Distinct(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19))

Res_Graph = Function('Resources_Graph', V_RES, V_RES, BoolSort())  # Declaring the Resources Graph
# Making the initialisation of the Graph
x, y = Consts('x y', V_RES)
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
s.add(ForAll([x, y], If(Or(And(x == r2, y == r1), And(x == r4, y == r3), And(x == r6, y == r1), And(x == r6, y == r2),
                           And(x == r6, y == r5), And(x == r7, y == r4), And(x == r7, y == r6), And(x == r8, y == r1),
                           And(x == r8, y == r4), And(x == r8, y == r6), And(x == r9, y == r0), And(x == r9, y == r1),
                           And(x == r10, y == r1), And(x == r10, y == r4), And(x == r10, y == r6),
                           And(x == r10, y == r8), And(x == r10, y == r9), And(x == r11, y == r0),
                           And(x == r11, y == r5), And(x == r11, y == r7), And(x == r11, y == r8),
                           And(x == r12, y == r0), And(x == r12, y == r1), And(x == r12, y == r4),
                           And(x == r12, y == r10), And(x == r12, y == r11), And(x == r13, y == r1),
                           And(x == r13, y == r5), And(x == r13, y == r6), And(x == r13, y == r8),
                           And(x == r13, y == r11), And(x == r13, y == r12), And(x == r14, y == r4),
                           And(x == r14, y == r5), And(x == r14, y == r6), And(x == r14, y == r7),
                           And(x == r14, y == r10), And(x == r15, y == r5), And(x == r15, y == r9),
                           And(x == r15, y == r10), And(x == r15, y == r12), And(x == r15, y == r14),
                           And(x == r16, y == r8), And(x == r16, y == r11), And(x == r16, y == r14),
                           And(x == r17, y == r3), And(x == r17, y == r12), And(x == r17, y == r13),
                           And(x == r17, y == r16), And(x == r18, y == r1), And(x == r18, y == r4),
                           And(x == r18, y == r5), And(x == r18, y == r10), And(x == r18, y == r15),
                           And(x == r18, y == r17), And(x == r19, y == r1), And(x == r19, y == r6),
                           And(x == r19, y == r8), And(x == r19, y == r14), And(x == r19, y == r15),
                           And(x == r19, y == r16), And(x == r19, y == r17), And(x == r19, y == r18)),
                        Res_Graph(x, y) == True, Res_Graph(x, y) == False)))

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
x, y = Consts('x y', V_RES)  # Constants to define the ForAll
expressionList1 = []  # List of expressions in the format Subject_Closure_Graph(x, y)
expressionList2 = []  # List of expressions in the format And(x == V_SUB.element, y == V_SUB.element)
for key in Python_Resource_Closure_Graph.keys():
    for node in Python_Resource_Closure_Graph[key]:
        expressionList1.append(Resource_Closure_Graph(key, node))
        expressionList2.append(And(x == key, y == node))

if expressionList1:  # If the expression list is not empty. The graph is not empty.
    for formula in expressionList1:
        s.add(formula)  # Adding the pairs to the solver
    s.add(ForAll([x, y], If(Or(expressionList2),
                            Resource_Closure_Graph(x, y) == True,
                            Resource_Closure_Graph(x, y) == False)))  # Making the remaining false.

rules = DeclareSort('rules')  # Creation of a rule type RULE_T in the B machine.
rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38,\
rule39 = Consts('rule30 rule31 rule32 rule33 rule34 rule35 rule36 rule37 rule38 rule39', rules)
s.add(Distinct(rule30, rule31, rule32, rule33, rule34, rule35, rule36, rule37, rule38, rule39))

MODALITY = DeclareSort('ModalityType')  # Creation of modality type.
permission, prohibition = Consts('permission prohibition', MODALITY)  # Creating modality elements.


CONTEXT = DeclareSort('Context')  # Creation of a context.
c0, c1, c2 = Consts('c0 c1 c2', CONTEXT)  # Going to change this later to predicates.


rule_subject = Function('rule_subject', rules, V_SUB, BoolSort())
rule_resource = Function('rule_resource', rules, V_RES, BoolSort())
rule_modality = Function('rule_modality', rules, MODALITY, BoolSort())
rule_priority = Function('rule_priority', rules, IntSort(), BoolSort())
rule_condition = Function('rule_condition', rules, CONTEXT, BoolSort())

# Adding the subject for each specific rule.
s.add(rule_subject(rule30, s19), rule_subject(rule31, s7), rule_subject(rule32, s11), rule_subject(rule33, s13),
      rule_subject(rule34, s3), rule_subject(rule35, s7), rule_subject(rule36, s13), rule_subject(rule37, s14),
      rule_subject(rule38, s8), rule_subject(rule39, s0))
x = Const('x', rules)
y = Const('y', V_SUB)
s.add(ForAll([x, y], If(Or(And(x == rule30, y == s19), And(x == rule31, y == s7), And(x == rule32, y == s11),
                           And(x == rule33, y == s13), And(x == rule34, y == s3), And(x == rule35, y == s7),
                           And(x == rule36, y == s13), And(x == rule37, y == s14), And(x == rule38, y == s8),
                           And(x == rule39, y == s0)),  # If any of this options
                        rule_subject(x, y) == True,  # Then True
                        rule_subject(x, y) == False)))  # Else -> False


# Adding the modality for each specific rule.
s.add(rule_modality(rule30, prohibition), rule_modality(rule31, permission), rule_modality(rule32, permission),
      rule_modality(rule33, permission), rule_modality(rule34, prohibition), rule_modality(rule35, prohibition),
      rule_modality(rule36, permission), rule_modality(rule37, prohibition), rule_modality(rule38, prohibition),
      rule_modality(rule39, permission))
x = Const('x', rules)
y = Const('y', MODALITY)
s.add(ForAll([x, y], If(Or(And(x == rule30, y == prohibition), And(x == rule31, y == permission),
                           And(x == rule32, y == permission), And(x == rule33, y == permission),
                           And(x == rule34, y == prohibition), And(x == rule35, y == prohibition),
                           And(x == rule36, y == permission), And(x == rule37, y == prohibition),
                           And(x == rule38, y == prohibition), And(x == rule39, y == permission)),  # If it is this
                        rule_modality(x, y) == True,  # Then True
                        rule_modality(x, y) == False)))  # Else -> False

# Adding the priority for each specific rule.
s.add(rule_priority(rule30, 1), rule_priority(rule31, 3), rule_priority(rule32, 4), rule_priority(rule33, 1),
      rule_priority(rule34, 3), rule_priority(rule35, 0), rule_priority(rule36, 1), rule_priority(rule37, 1),
      rule_priority(rule38, 0), rule_priority(rule39, 1))
x = Const('x', rules)
y = Const('y', IntSort())
s.add(ForAll([x, y], If(Or(And(x == rule30, y == 1), And(x == rule31, y == 3), And(x == rule32, y == 4),
                           And(x == rule33, y == 1), And(x == rule34, y == 3), And(x == rule35, y == 0),
                           And(x == rule36, y == 1), And(x == rule37, y == 1), And(x == rule38, y == 0),
                           And(x == rule39, y == 1)),  # If it is this
                        rule_priority(x, y) == True,  # Then True
                        rule_priority(x, y) == False)))  # Else -> False


# Adding the lessSpecific constant as a z3 relation between rules.
lessSpecific = Function('lessSpecific', rules, rules, BoolSort())
rule1, rule2 = Consts('rule1 rule2', rules)  # Auxiliary variables to the declaration of the predicate of lessSpecific.
x, y = Consts('x y', IntSort())  # Auxiliary variables to the declaration of the predicate of lessSpecific.
w, z = Consts('w z', V_SUB)  # Auxiliary variables to the declaration of the predicate of lessSpecific.
s.add(ForAll([rule1, rule2, x, y, w, z],
             Implies(And(rule_priority(rule1, x), rule_priority(rule2, y),
                         rule_subject(rule1, w), rule_subject(rule2, z), rule1 != rule2,
                         Or(x > y, And(x == y, Subject_Closure_Graph(w, z)))
                         ), lessSpecific(rule1, rule2))))  # Formula that fits lessSpecific.


# Adding the resource for each specific rule.
s.add(rule_resource(rule30, r17), rule_resource(rule31, r0), rule_resource(rule32, r14), rule_resource(rule33, r6),
      rule_resource(rule34, r8), rule_resource(rule35, r11), rule_resource(rule36, r6), rule_resource(rule37, r4),
      rule_resource(rule38, r15), rule_resource(rule39, r14))
x = Const('x', rules)
y = Const('y', V_RES)
s.add(ForAll([x, y], If(Or(And(x == rule30, y == r17), And(x == rule31, y == r0), And(x == rule32, y == r14),
                           And(x == rule33, y == r6), And(x == rule34, y == r8), And(x == rule35, y == r11),
                           And(x == rule36, y == r6), And(x == rule37, y == r4), And(x == rule38, y == r15),
                           And(x == rule39, y == r14)),  # If any of this options
                        rule_resource(x, y) == True,  # Then True
                        rule_resource(x, y) == False)))  # Else -> False

# Adding the resource for each specific rule.
s.add(rule_condition(rule30, c2), rule_condition(rule30, c0), rule_condition(rule31, c0), rule_condition(rule31, c2),
      rule_condition(rule32, c0), rule_condition(rule33, c1), rule_condition(rule33, c0), rule_condition(rule34, c2),
      rule_condition(rule35, c0), rule_condition(rule35, c2), rule_condition(rule36, c1), rule_condition(rule37, c2),
      rule_condition(rule38, c2), rule_condition(rule38, c0), rule_condition(rule39, c0), rule_condition(rule39, c1))
x = Const('x', rules)
y = Const('y', CONTEXT)
s.add(ForAll([x, y], If(Or(And(x == rule30, y == c2), And(x == rule30, y == c0), And(x == rule31, y == c0),
                           And(x == rule31, y == c2), And(x == rule32, y == c0), And(x == rule33, y == c1),
                           And(x == rule33, y == c0), And(x == rule34, y == c2), And(x == rule35, y == c0),
                           And(x == rule35, y == c2), And(x == rule36, y == c1), And(x == rule37, y == c2),
                           And(x == rule38, y == c2), And(x == rule38, y == c0), And(x == rule39, y == c0),
                           And(x == rule39, y == c1)),  # If any of this options
                        rule_condition(x, y) == True,  # Then True
                        rule_condition(x, y) == False)))  # Else -> False


REQUEST_T = Function('REQUEST_T', V_SUB, V_RES, BoolSort())
notDomainSUB = Function('notDomainSub', V_SUB, BoolSort())
notDomainRES = Function('notDomainRES', V_RES, BoolSort())
sub1, sub2 = Consts('sub1 sub2', V_SUB)  # Auxiliary variables to the declaration of the predicate of REQUEST_T.
res1, res2 = Consts('res1 res2', V_RES)  # Auxiliary variables to the declaration of the predicate of REQUEST_T.
s.add(ForAll(sub1, If(Not(Exists(sub2, Sub_Graph(sub1, sub2))), notDomainSUB(sub1), notDomainSUB(sub1) == False)))
# Formulas to describe REQUEST_T
s.add(ForAll(res1, If(Not(Exists(res2, Res_Graph(res1, res2))), notDomainRES(res1), notDomainRES(res1) == False)))
s.add(ForAll([sub1, res1], Implies(And(notDomainSUB(sub1), notDomainRES(res1)), REQUEST_T(sub1, res1))))

conRule = Function('conRule', CONTEXT, rules, BoolSort())  # Creating of the variable ConRule
auxCon = Const('auxCon', CONTEXT)
auxRule = Const('auxRule', rules)
s.add(ForAll([auxCon, auxRule], Implies(rule_condition(auxRule, auxCon), conRule(auxCon, auxRule))))


if s.check():
    print(s.model()[notDomainRES])
