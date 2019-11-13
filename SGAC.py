from z3 import *
import re
#import time

def SGAC_random(testName, dir, testNumber):
    #ts = time.time()

    set_param(max_width=3000)
    set_param(max_depth=5000000000000000000000000000000000000)
    set_param(max_args=10000000000000000000000000000000000000)
    set_param(max_lines=10000000000000)
    set_param(max_indent=100000000000000000)
    set_param(memory_max_size=429496729500000)

    s = Solver()  # Declaring the Z3 solver and storing it to the variable s.

    Python_Sub_Graph_Text = dict()
    Python_Sub_Graph = dict()
    Python_Res_Graph_Text = dict()
    Python_Res_Graph = dict()
    Python_Rules_Text_Dict = dict()
    Python_Sub_Closure_Graph_Text = dict()
    Python_Res_Closure_Graph_Text = dict()
    '''
    Describing the SETS and PROPERTIES clauses fo the B machine.
    '''

    # Reading the Subject Graph
    V_SUB = DeclareSort('Vertex_Subject')  # Declaring a type 'Vertex_Subject' (Vertex of the Subject Graph)
    auxSub1, auxSub2 = Consts('auxSub1 auxSub2', V_SUB)

    V_RES = DeclareSort('Vertex_Resource')  # Declaring a type 'Vertex_Resource' (Vertex of the Resource Graph)
    auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)

    MODALITY = DeclareSort('ModalityType')  # Creation of modality type.
    permission, prohibition = Consts('permission prohibition', MODALITY)  # Creating modality elements.
    auxModality = Const('auxModality', MODALITY)
    s.add(Distinct(permission, prohibition))

    CONTEXT = DeclareSort('Context')  # Creation of a context.
    auxCon = Const('auxCon', CONTEXT)

    rules = DeclareSort('rules')  # Creation of a rule type RULE_T in the B machine.
    auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
    auxInt = Const('auxInt', IntSort())

    with open(dir + os.sep + "SGAC_random_"+str(testNumber)+".txt", 'r') as f:
        Python_Sub_Text = f.readline()
        matches = re.finditer(r"'+s[0-9]':", Python_Sub_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Sub_Graph_Text[(Python_Sub_Text[match.start():match.end()].replace("'", "").replace(":", ""))] = []
        matches = re.finditer(r"\[.*?\]", Python_Sub_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Sub_Graph_Text["s"+str(matchNum-1)] = Python_Sub_Text[match.start():match.end()]
        Python_Res_Text = f.readline()
        matches = re.finditer(r"'+r[0-9]':", Python_Res_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Res_Graph_Text[(Python_Res_Text[match.start():match.end()].replace("'", "").replace(":", ""))] = []
        matches = re.finditer(r"\[.*?\]", Python_Res_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Res_Graph_Text["r" + str(matchNum - 1)] = Python_Res_Text[match.start():match.end()]
        Python_Context_List = eval(f.readline())
        Python_Rules_Text = f.readline()
        Python_Rules_list = []
        matches = re.finditer(r"'+rule[0-9]+':", Python_Rules_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Rules_Text_Dict[(Python_Rules_Text[match.start():match.end()].replace("'", "").replace(":", ""))] = []
            Python_Rules_list.append(Python_Rules_Text[match.start():match.end()].replace("'", "").replace(":", ""))
        matches = re.finditer(r"\[.*?\]\]", Python_Rules_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Rules_Text_Dict[Python_Rules_list[matchNum - 1]] = eval(Python_Rules_Text[match.start():match.end()])
        Python_Sub_Closure_Text = f.readline()
        matches = re.finditer(r"'+s[0-9]':", Python_Sub_Closure_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Sub_Closure_Graph_Text[(Python_Sub_Closure_Text[match.start():match.end()].replace("'",
                                                                                                      "").replace(":",
                                                                                                                  ""))] = []
        matches = re.finditer(r"\[.*?\]", Python_Sub_Closure_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Sub_Closure_Graph_Text["s" + str(matchNum - 1)] = Python_Sub_Closure_Text[match.start():match.end()]
        Python_Res_Closure_Text = f.readline()
        matches = re.finditer(r"'+r[0-9]':", Python_Res_Closure_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Res_Closure_Graph_Text[(Python_Res_Closure_Text[match.start():match.end()].replace("'",
                                                                                                      "").replace(":",
                                                                                                                  ""))] = []
        matches = re.finditer(r"\[.*?\]", Python_Res_Closure_Text, re.MULTILINE)
        for matchNum, match in enumerate(matches, start=1):
            Python_Res_Closure_Graph_Text["r" + str(matchNum - 1)] = Python_Res_Closure_Text[match.start():match.end()]


    for key in Python_Sub_Graph_Text.keys():
        globals()['%s' % key] = Const(key, V_SUB)
        Python_Sub_Graph[eval(key)] = []
        for node in eval(Python_Sub_Graph_Text[key]):
            Python_Sub_Graph[eval(key)].append(node)

    predicate = "Distinct("
    for sub in Python_Sub_Graph.keys():
        predicate += str(sub)+", "
    predicate = predicate[:len(predicate)-2:]+")"
    s.add(eval(predicate))

    Sub_Graph = Function('Subject_Graph', V_SUB, V_SUB, BoolSort())
    Subject_Closure_Graph = Function('Transitive_Closure_Subject_Graph', V_SUB, V_SUB, BoolSort())

    predicate = "ForAll([auxSub1, auxSub2], If(Or("
    predicate_closure = "ForAll([auxSub1, auxSub2], If(Or("
    predicate_sub1 = "Not(Exists([auxSub1, auxSub2], And(And("
    predicate_sub2 = "And("
    for sub in Python_Sub_Graph.keys():
        for child in Python_Sub_Graph[sub]:
            predicate += "And(auxSub1 == " + str(sub) + ", auxSub2 == " + str(child) + "), "
        for child in eval(Python_Sub_Closure_Graph_Text[str(sub)]):
            predicate_closure += "And(auxSub1 == " + str(sub) + ", auxSub2 == " + str(child) + "), "
        predicate_sub1 += "auxSub1 != " + str(sub) + ", "
        predicate_sub2 += "auxSub2 != " + str(sub) + ", "
    predicate = predicate[:len(predicate)-2:]
    predicate_closure = predicate_closure[:len(predicate_closure)-2:]
    predicate += "), Sub_Graph(auxSub1, auxSub2) == True, Sub_Graph(auxSub1, auxSub2) == False))"
    predicate_closure += "), Subject_Closure_Graph(auxSub1, auxSub2) == True," \
                         " Subject_Closure_Graph(auxSub1, auxSub2) == False))"
    predicate_sub1 = predicate_sub1[:len(predicate_sub1)-2:] + "), " + predicate_sub2[:len(predicate_sub2)-2:] + "))))"
    s.add(eval(predicate))
    s.add(eval(predicate_closure))
    s.add(eval(predicate_sub1))

    for key in Python_Res_Graph_Text.keys():
        globals()['%s' % key] = Const(key, V_RES)
        Python_Res_Graph[eval(key)] = []
        for node in eval(Python_Res_Graph_Text[key]):
            Python_Res_Graph[eval(key)].append(node)

    predicate = "Distinct("
    for res in Python_Res_Graph.keys():
        predicate += str(res)+", "
    predicate = predicate[:len(predicate)-2:]+")"
    s.add(eval(predicate))

    Res_Graph = Function('Resources_Graph', V_RES, V_RES, BoolSort())  # Declaring the Resources Graph
    Resource_Closure_Graph = Function('Transitive_Closure_Resources_Graph', V_RES, V_RES, BoolSort())

    predicate = "ForAll([auxRes1, auxRes2], If(Or("
    predicate_closure = "ForAll([auxRes1, auxRes2], If(Or("
    predicate_res1 = "Not(Exists([auxRes1, auxRes2], And(And("
    predicate_res2 = "And("
    for res in Python_Res_Graph.keys():
        for child in Python_Res_Graph[res]:
            predicate += "And(auxRes1 == "+str(res)+", auxRes2 == "+str(child)+"), "
        for child in eval(Python_Res_Closure_Graph_Text[str(res)]):
            predicate_closure += "And(auxRes1 == "+str(res)+", auxRes2 == "+str(child)+"), "
        predicate_res1 += "auxRes1 != " + str(res) + ", "
        predicate_res2 += "auxRes2 != " + str(res) + ", "
    predicate = predicate[:len(predicate)-2:]
    predicate_closure = predicate_closure[:len(predicate_closure)-2:]
    predicate += "), Res_Graph(auxRes1, auxRes2) == True, Res_Graph(auxRes1, auxRes2) == False))"
    predicate_closure += "), Resource_Closure_Graph(auxRes1, auxRes2) == True," \
                         " Resource_Closure_Graph(auxRes1, auxRes2) == False))"
    predicate_res1 = predicate_res1[:len(predicate_res1)-2:] + "), " + predicate_res2[:len(predicate_res2)-2:] + "))))"
    s.add(eval(predicate))
    s.add(eval(predicate_closure))
    s.add(eval(predicate_res1))

    for context in Python_Context_List:
        globals()['%s' % context] = Const(context, CONTEXT)

    predicate = "Distinct("
    for context in Python_Context_List:
        predicate += str(context)+", "
    predicate = predicate[:len(predicate)-2:]+")"
    s.add(eval(predicate))

    predicate_rule_subject = "ForAll([auxRule1, auxSub1], If(Or("
    predicate_rule_resource = "ForAll([auxRule1, auxRes1], If(Or("
    predicate_rule_modality = "ForAll([auxRule1, auxModality], If(Or("
    predicate_rule_priority = "ForAll([auxRule1, auxInt], If(Or("
    predicate_rule_context = "ForAll([auxRule1, auxCon], If(Or("
    predicate_rule_distinct = "Distinct("
    for key in Python_Rules_Text_Dict.keys():
        globals()['%s' % key] = Const(key, rules)
        predicate_rule_subject += "And(auxRule1 == " + str(key) + ", auxSub1 == " + str(
            Python_Rules_Text_Dict[key][0]) + "), "
        predicate_rule_resource += "And(auxRule1 == " + str(key) + ", auxRes1 == " + str(
            Python_Rules_Text_Dict[key][1]) + "), "
        predicate_rule_modality += "And(auxRule1 == " + str(key) + ", auxModality == " + str(
            Python_Rules_Text_Dict[key][2]) + "), "
        predicate_rule_priority += "And(auxRule1 == " + str(key) + ", auxInt == " + str(
            Python_Rules_Text_Dict[key][3]) + "), "
        for context in Python_Rules_Text_Dict[key][4]:
            predicate_rule_context += "And(auxRule1 == " + str(key) + ", auxCon == " + str(context) + "), "
        predicate_rule_distinct += str(key) + ", "
    predicate_rule_subject = predicate_rule_subject[:len(predicate_rule_subject)-2:]
    predicate_rule_subject += "), rule_subject(auxRule1, auxSub1) == True, rule_subject(auxRule1, auxSub1) == False))"
    predicate_rule_resource = predicate_rule_resource[:len(predicate_rule_resource)-2:]
    predicate_rule_resource += "), rule_resource(auxRule1, auxRes1) == True, rule_resource(auxRule1, auxRes1) == False))"
    predicate_rule_modality = predicate_rule_modality[:len(predicate_rule_modality)-2:]
    predicate_rule_modality += "), rule_modality(auxRule1, auxModality) == True," \
                               " rule_modality(auxRule1, auxModality) == False))"
    predicate_rule_priority = predicate_rule_priority[:len(predicate_rule_priority)-2:]
    predicate_rule_priority += "), rule_priority(auxRule1, auxInt) == True, rule_priority(auxRule1, auxInt) == False))"
    predicate_rule_context = predicate_rule_context[:len(predicate_rule_context)-2:]
    predicate_rule_context += "), rule_condition(auxRule1, auxCon) == True, rule_condition(auxRule1, auxCon) == False))"
    predicate_rule_distinct = predicate_rule_distinct[:len(predicate_rule_distinct)-2:] + ")"


    rule_subject = Function('rule_subject', rules, V_SUB, BoolSort())
    rule_resource = Function('rule_resource', rules, V_RES, BoolSort())
    rule_modality = Function('rule_modality', rules, MODALITY, BoolSort())
    rule_priority = Function('rule_priority', rules, IntSort(), BoolSort())
    rule_condition = Function('rule_condition', rules, CONTEXT, BoolSort())

    s.add(eval(predicate_rule_subject))
    s.add(eval(predicate_rule_resource))
    s.add(eval(predicate_rule_modality))
    s.add(eval(predicate_rule_priority))
    s.add(eval(predicate_rule_context))
    s.add(eval(predicate_rule_distinct))

    # Adding the REQUEST_T constant as a z3 relation between (V_SUB-dom(e_sub)) * (V_RES-dom(e_res))
    REQUEST_T = Function('REQUEST_T', V_SUB, V_RES, BoolSort())
    notDomainSUB = Function('notDomainSub', V_SUB, BoolSort())
    notDomainRES = Function('notDomainRes', V_RES, BoolSort())
    s.add(ForAll(auxSub1, If(Not(Exists(auxSub2, Sub_Graph(auxSub1, auxSub2))),
                             notDomainSUB(auxSub1), notDomainSUB(auxSub1) == False)))
    s.add(ForAll(auxRes1, If(Not(Exists(auxRes2, Res_Graph(auxRes1, auxRes2))),
                             notDomainRES(auxRes1), notDomainRES(auxRes1) == False)))
    s.add(ForAll([auxSub1, auxRes1], Implies(And(notDomainSUB(auxSub1),
                                                 notDomainRES(auxRes1)),
                                             REQUEST_T(auxSub1, auxRes1))))
    s.add(Implies(REQUEST_T(auxSub1, auxRes1), And(notDomainSUB(auxSub1),
                                                   notDomainRES(auxRes1))))

    predicate1 = "Implies(notDomainSUB(auxSub1), And(Not(Exists(auxSub2, Sub_Graph(auxSub1, auxSub2))), Or("
    predicate2 = "Implies(notDomainRES(auxRes1), And(Not(Exists(auxRes2, Res_Graph(auxRes1, auxRes2))), Or("
    predicate3 = "Not(Exists([auxSub1, auxRes1], Or(And("
    for sub in Python_Sub_Graph.keys():
        predicate1 += "auxSub1 == "+str(sub)+", "
        predicate3 += "auxSub1 == "+str(sub)+", "
    predicate3 = predicate3[:len(predicate3)-2:] + "), And("
    for res in Python_Res_Graph.keys():
        predicate2 += "auxRes1 == "+str(res)+", "
        predicate3 += "auxRes1 == "+str(res)+", "
    predicate1 = predicate1[:len(predicate1)-2:]+")))"
    predicate2 = predicate2[:len(predicate2)-2:]+")))"
    predicate3 = predicate3[:len(predicate3)-2:]+"))))"
    s.add(eval(predicate1))
    s.add(eval(predicate2))
    s.add(eval(predicate3))

    # Adding the lessSpecific constant as a z3 relation between rules.
    lessSpecific = Function('lessSpecific', rules, rules, BoolSort())
    auxInt1, auxInt2 = Consts('auxInt1 auxInt2', IntSort())
    s.add(Implies(lessSpecific(auxRule1, auxRule2),
                  And(rule_priority(auxRule1, auxInt1), rule_priority(auxRule2, auxInt2),
                      rule_subject(auxRule1, auxSub1), rule_subject(auxRule2, auxSub2),
                      auxRule1 != auxRule2,
                      Or(auxInt1 > auxInt2, And(auxInt1 == auxInt2, Subject_Closure_Graph(auxSub1, auxSub2)))
                      )
                  )

          )
    s.add((Or(auxInt1 != 0, auxInt1 != 1, auxInt1 != 2, auxInt1 != 3, auxInt1 != 4)))
    s.add((Or(auxInt2 != 0, auxInt2 != 1, auxInt2 != 2, auxInt2 != 3, auxInt2 != 4)))
    # s.add(Not(Exists([auxInt1, auxInt2],
    #                  And(And(auxInt1 != 0, auxInt1 != 1, auxInt1 != 2, auxInt1 != 3, auxInt1 != 4),
    #                      And(And(auxInt2 != 0, auxInt2 != 1, auxInt2 != 2, auxInt2 != 3, auxInt2 != 4))))))
    s.add(ForAll([auxRule1, auxRule2, auxInt1, auxInt2, auxSub1, auxSub2],
                 Implies(And(rule_priority(auxRule1, auxInt1), rule_priority(auxRule2, auxInt2),
                             rule_subject(auxRule1, auxSub1), rule_subject(auxRule2, auxSub2),
                             auxRule1 != auxRule2,
                             Or(auxInt1 > auxInt2, And(auxInt1 == auxInt2,
                                                       Subject_Closure_Graph(auxSub1, auxSub2)))),
                         lessSpecific(auxRule1, auxRule2))))  # Formula that fits lessSpecific.

    conRule = Function('conRule', CONTEXT, rules, BoolSort())  # Creating of the variable ConRule
    s.add(ForAll([auxCon, auxRule1], Implies(rule_condition(auxRule1, auxCon), conRule(auxCon, auxRule1))))
    s.add(Implies(conRule(auxCon, auxRule1), rule_condition(auxRule1, auxCon)))

    applicable = Function('applicable', V_SUB, V_RES, rules, BoolSort())  # Declaring VARIABLE applicable
    # Defining the applicable variable
    s.add(Implies(applicable(auxSub1, auxRes1, auxRule1),
                  And(Or(rule_subject(auxRule1, auxSub1),
                         And(Subject_Closure_Graph(auxSub2, auxSub1),
                             rule_subject(auxRule1, auxSub2))
                         ),
                      Or(rule_resource(auxRule1, auxRes1),
                         And(rule_resource(auxRule1, auxRes2),
                             Resource_Closure_Graph(auxRes2, auxRes1))
                         ),
                      REQUEST_T(auxSub1, auxRes1)
                      )
                  )
          )
    s.add(ForAll([auxRes1, auxSub2, auxRule1, auxRes2, auxSub1], Implies(And(Or(rule_subject(auxRule1, auxSub1),
                                                                               And(rule_subject(auxRule1, auxSub2),
                                                                                   Subject_Closure_Graph(auxSub2,
                                                                                                         auxSub1))),
                                                                            Or(rule_resource(auxRule1, auxRes1),
                                                                               And(rule_resource(auxRule1, auxRes2),
                                                                                   Resource_Closure_Graph(auxRes2, auxRes1))
                                                                               ),
                                                                            REQUEST_T(auxSub1, auxRes1)
                                                                            ),
                                                                        applicable(auxSub1, auxRes1, auxRule1))
                 )
          )
    #t1 = time.time()
    #print("Time to start the first check:", t1 - ts)

    print(s.check())
    #t2 = time.time()
    #print("Time to finish the check:", t2 - t1)
    if s.check() == sat:
        f = open(dir + os.sep + testName+"_MODEL1.txt", "w+")
        for variable in s.model():
            f.write(str(variable)), f.write("="), f.write(str(s.model()[variable])), f.write("\n")
        f.close()

        dictOfSubstitutions = dict()
        chosenVariables = [permission, prohibition]
        for sub in Python_Sub_Graph.keys():
            chosenVariables.append(sub)
        for res in Python_Res_Graph.keys():
            chosenVariables.append(res)
        for key in Python_Rules_Text_Dict.keys():
            chosenVariables.append(eval(key))
        for context in Python_Context_List:
            chosenVariables.append(eval(context))

        for variable in chosenVariables:
            with open(dir + os.sep + testName+"_MODEL1.txt") as f:
                for line in f:
                    matches = re.finditer(r"^" + str(variable) + "=", line)
                    for matchNum, match in enumerate(matches):
                        dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
            f.close()
        with open(dir + os.sep + testName+"_MODEL1.txt", 'r') as f:
            modelContent = f.read()
        f.close()
        for key in dictOfSubstitutions.keys():
            modelContent = re.sub(r"" + str(dictOfSubstitutions[key]) + "", str(key), modelContent)
        # Erasing the k!#### and replacing for the variables
        modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
        # Erasing k!#### variables
        modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
        # Erasing weird syntax from the solver (If(Var(0) == ...)
        modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "", modelContent)
        modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
        modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
        # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
        modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
        modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
        modelContent = re.sub(r"\[ Or", "[Or", modelContent)
        f = open(dir + os.sep + testName+"_MODEL1.txt", "w+")
        f.write(modelContent)
        f.close()

        # Rewriting the model for rerun in another Z3 model and accomplish the Exists quantification
        # Adding a new solver
        r = Solver()
        dictOfFormulas = dict()

        formulas = [Sub_Graph, Subject_Closure_Graph, Res_Graph, Resource_Closure_Graph, REQUEST_T, rule_subject,
                    rule_resource, rule_modality, rule_priority, rule_condition, lessSpecific, conRule, applicable,
                    notDomainSUB, notDomainRES]
        with open(dir + os.sep + testName+"_MODEL1.txt", 'r') as f:
            modelContent = f.read()

        for formula in formulas:
            if re.search(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE) is not None:
                matches = re.finditer(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE)
                for matchNum, match in enumerate(matches, start=1):
                    dictOfFormulas[formula.name()] = modelContent[match.start() + len(formula.name()) + 2:match.end() - 1:]
            else:
                matches = re.finditer(r"%s=\[.*?\n\s*.*?\]" % formula.name(), modelContent, re.MULTILINE | re.DOTALL)
                for matchNum, match in enumerate(matches, start=1):
                    dictOfFormulas[formula.name()] = modelContent[match.start() + len(formula.name()) + 2:match.end() - 1:]

        predicate_subject = "Distinct("
        predicate_resource = "Distinct("
        predicate_rule = "Distinct("
        predicate_rule1 = "Not(Exists([auxRule1, auxRule2], And(And("
        # predicate_rule2 = "Or("
        predicate_context_distinct = "Distinct("
        predicate_context = "Not(Exists(auxCon, And("
        for sub in Python_Sub_Graph.keys():
            predicate_subject += str(sub)+", "
        for res in Python_Res_Graph.keys():
            predicate_resource += str(res)+", "
        for key in Python_Rules_Text_Dict.keys():
            predicate_rule += str(key)+", "
            predicate_rule1 += "auxRule1 != " + str(key) + ", "
            # predicate_rule2 += "auxRule2 == " + str(key) + ", "
        for context in Python_Context_List:
            predicate_context_distinct += str(context)+", "
            predicate_context += "auxCon != " + str(context) + ", "

        predicate_subject = predicate_subject[:len(predicate_subject)-2:] + ")"
        predicate_resource = predicate_resource[:len(predicate_resource) - 2:] + ")"
        predicate_rule = predicate_rule[:len(predicate_rule) - 2:] + ")"
        predicate_rule1 = predicate_rule1[:len(predicate_rule1) - 2:] + "), " + predicate_rule1[
                                                                                37:len(predicate_rule1) - 2:].replace(
            "auxRule1", "auxRule2") + "))))"
        # predicate_rule2 = predicate_rule2[:len(predicate_rule2) - 2:] + ")"
        predicate_context_distinct = predicate_context_distinct[:len(predicate_context_distinct) - 2:] + ")"
        predicate_context = predicate_context[:len(predicate_context)-2:] + ")))"

        r.add(eval(predicate_subject))
        r.add(eval(predicate_resource))
        r.add(eval(predicate_rule))
        r.add(eval(predicate_rule1))
        # r.add(eval(predicate_rule2))
        r.add(eval(predicate_context_distinct))
        r.add(eval(predicate_res1), eval(predicate_sub1))
        r.add(Distinct(permission, prohibition))
        r.add(eval(predicate_context))
        for formula in dictOfFormulas.keys():
            if formula == 'Subject_Graph':
                predicate = eval(
                    dictOfFormulas['Subject_Graph'].replace(', s', ', auxSub2 == s').replace('And(s', 'And(auxSub1 == s'))
                r.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                    Sub_Graph(auxSub1, auxSub2) == True,
                                                    Sub_Graph(auxSub1, auxSub2) == False)
                             )
                      )
            if formula == 'Resources_Graph':
                predicate = eval(
                    dictOfFormulas['Resources_Graph'].replace(', r', ', auxRes2 == r').replace('And(r', 'And(auxRes1 == r'))
                r.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                    Res_Graph(auxRes1, auxRes2) == True,
                                                    Res_Graph(auxRes1, auxRes2) == False)
                             )
                      )
            if formula == 'Transitive_Closure_Subject_Graph':
                predicate = eval(
                    dictOfFormulas['Transitive_Closure_Subject_Graph'].replace(', s', ', auxSub2 == s').replace('And(s', 'And(auxSub1 == s'))
                r.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                    Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                                    Subject_Closure_Graph(auxSub1, auxSub2) == False)
                             )
                      )
            if formula == 'Transitive_Closure_Resources_Graph':
                predicate = eval(
                    dictOfFormulas['Transitive_Closure_Resources_Graph'].replace(', r', ', auxRes2 == r').replace('And(r', 'And(auxRes1 == r'))
                r.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                    Resource_Closure_Graph(auxRes1, auxRes2) == True,
                                                    Resource_Closure_Graph(auxRes1, auxRes2) == False)
                             )
                      )
            if formula == 'REQUEST_T':
                predicate = eval(
                    dictOfFormulas['REQUEST_T'].replace(', r', ', auxRes1 == r').replace('And(s', 'And(auxSub1 == s'))
                r.add(ForAll([auxSub1, auxRes1], If(predicate,
                                                    REQUEST_T(auxSub1, auxRes1) == True,
                                                    REQUEST_T(auxSub1, auxRes1) == False)))

            if formula == 'rule_modality':
                predicate = eval(
                    dictOfFormulas['rule_modality'].replace('Not(p', 'Not(auxModality == p').replace(
                        'Not(rule', 'Not(auxRule1 == rule'))
                # predicate = eval(
                #     dictOfFormulas['rule_modality'].replace(')))', ")").replace('), Not(p', ', auxModality == p').replace(
                #         'Not(Or(Not(rule', 'And(auxRule1 == rule'))
                r.add(ForAll([auxRule1, auxModality], If(predicate,  # If it is this
                                                         rule_modality(auxRule1, auxModality) == True,  # Then True
                                                         rule_modality(auxRule1, auxModality) == False)))  # Else -> False)

            if formula == 'rule_subject':
                predicate = eval(
                    dictOfFormulas['rule_subject'].replace(', s', ', auxSub1 == s').replace(
                        'And(rule', 'And(auxRule1 == rule'))
                r.add(ForAll([auxRule1, auxSub1], If(predicate,  # If it is this
                                                     rule_subject(auxRule1, auxSub1) == True,  # Then True
                                                     rule_subject(auxRule1, auxSub1) == False)))  # Else -> False)

            if formula == 'rule_resource':
                predicate = eval(
                    dictOfFormulas['rule_resource'].replace(', r', ', auxRes1 == r').replace(
                        'And(rule', 'And(auxRule1 == rule'))
                r.add(ForAll([auxRule1, auxRes1], If(predicate,  # If it is this
                                                     rule_resource(auxRule1, auxRes1) == True,  # Then True
                                                     rule_resource(auxRule1, auxRes1) == False)))  # Else -> False)

            if formula == 'rule_condition':
                predicate = eval(dictOfFormulas['rule_condition'].replace(
                    ', c', ', auxCon == c').replace('And(rule', 'And(auxRule1 == rule'))
                r.add(ForAll([auxRule1, auxCon], If(predicate,  # If it is this
                                                    rule_condition(auxRule1, auxCon) == True,  # Then True
                                                    rule_condition(auxRule1, auxCon) == False)))  # Else -> False))

            if formula == 'rule_priority':
                predicate = eval(dictOfFormulas['rule_priority'].replace(', 4', ', auxInt == 4').replace(
                    ', 2', ', auxInt == 2').replace(', 3', ', auxInt == 3').replace(', 0', ', auxInt == 0').replace(
                    ', 1', ', auxInt == 1').replace('And(rule', 'And(auxRule1 == rule'))
                r.add(ForAll([auxRule1, auxInt], If(predicate,  # If it is this
                                                    rule_priority(auxRule1, auxInt) == True,  # Then True
                                                    rule_priority(auxRule1, auxInt) == False)))  # Else -> False))

            if formula == 'lessSpecific':
                predicate = eval(dictOfFormulas['lessSpecific'].replace(', r', ', auxRule2 == r').replace(
                    'And(r', 'And(auxRule1 == r'))
                r.add(ForAll([auxRule1, auxRule2], If(predicate,
                                                      lessSpecific(auxRule1, auxRule2),
                                                      Not(lessSpecific(auxRule1, auxRule2)))))

            if formula == 'conRule':
                predicate = eval(dictOfFormulas['conRule'].replace(', r', ', auxRule1 == r').replace(
                    'And(c', 'And(auxCon == c'))
                r.add(ForAll([auxRule1, auxCon], If(predicate,
                                                    conRule(auxCon, auxRule1),
                                                    Not(conRule(auxCon, auxRule1)))))

            if formula == 'applicable':
                predicate = eval(dictOfFormulas['applicable'].replace(
                    ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s', 'And(auxSub1 == s'))
                r.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                              applicable(auxSub1, auxRes1, auxRule1),
                                                              Not(applicable(auxSub1, auxRes1, auxRule1)))))

            if formula == 'notDomainSub':
                if "(s" in dictOfFormulas['notDomainSub']:
                    predicate = eval(dictOfFormulas['notDomainSub'].replace('(s', '(auxSub1 == s').replace(', s',
                                                                                                           ', auxSub1 == s'))
                else:
                    predicate = eval(dictOfFormulas['notDomainSub'].replace('s', 'auxSub1 == s'))
                r.add(ForAll([auxSub1], If(predicate,
                                           notDomainSUB(auxSub1),
                                           Not(notDomainSUB(auxSub1)))))

            if formula == 'notDomainRes':
                if "(r" in dictOfFormulas['notDomainRes']:
                    predicate = eval(dictOfFormulas['notDomainRes'].replace('(r', '(auxRes1 == r').replace(', r',
                                                                                                           ', auxRes1 == r'))
                else:
                    predicate = eval(dictOfFormulas['notDomainRes'].replace('r', 'auxRes1 == r'))
                r.add(ForAll([auxRes1], If(predicate,
                                           notDomainRES(auxRes1),
                                           Not(notDomainRES(auxRes1)))))

            maxElem = Function('maxElem', V_SUB, V_RES, rules, BoolSort())
            auxRes1 = Const('auxRes1', V_RES)
            auxSub1 = Const('auxSub1', V_SUB)
            auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
            r.add(ForAll([auxSub1, auxRes1, auxRule1], If(And(applicable(auxSub1, auxRes1, auxRule1),
                                                              Not(Exists(auxRule2,
                                                                         And(applicable(auxSub1, auxRes1, auxRule2),
                                                                             lessSpecific(auxRule1, auxRule2))))),
                                                          maxElem(auxSub1, auxRes1, auxRule1),
                                                          Not(maxElem(auxSub1, auxRes1, auxRule1)))))

        #t3 = time.time()
        #print("Time to start the second check:", t3 - ts)
        print(r.check())
        #t4 = time.time()
        #print("Time to finish the second check", t4 - t3)
        if r.check() == sat:
            # print(r.model()[isPrecededBy])
            f = open(dir + os.sep + testName+"_MODEL2.txt", "w+")
            for variable in r.model():
                f.write(str(variable)), f.write("="), f.write(str(r.model()[variable])), f.write("\n")
            f.close()

            dictOfSubstitutions = dict()
            chosenVariables = [permission, prohibition]
            for sub in Python_Sub_Graph.keys():
                chosenVariables.append(sub)
            for res in Python_Res_Graph.keys():
                chosenVariables.append(res)
            for key in Python_Rules_Text_Dict.keys():
                chosenVariables.append(eval(key))
            for context in Python_Context_List:
                chosenVariables.append(eval(context))

            # Rewriting the variables
            for variable in chosenVariables:
                with open(dir + os.sep + testName+"_MODEL2.txt") as f:
                    for line in f:
                        matches = re.finditer(r"^" + str(variable) + "=", line)
                        for matchNum, match in enumerate(matches):
                            dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
                f.close()

            with open(dir + os.sep + testName+"_MODEL2.txt", 'r') as f:
                modelContent = f.read()
            f.close()
            for key in dictOfSubstitutions.keys():
                modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0, re.MULTILINE)
            # Erasing the k!#### and replacing for the variables
            modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
            # Erasing k!#### variables
            modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
            # Erasing weird syntax from the solver (If(Var(0) == ...)
            modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "",
                                  modelContent)
            modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
            modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
            # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
            modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
            modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
            modelContent = re.sub(r"\[ Or", "[Or", modelContent)
            f = open(dir + os.sep + testName+"_MODEL2.txt", "w+")
            f.write(modelContent)
            f.close()

            # Rewriting the model for rerun in another Z3 model and accomplish the Exists quantification
            # Adding a new solver
            q = Solver()
            dictOfFormulas = dict()

            formulas = [Sub_Graph, Subject_Closure_Graph, Res_Graph, Resource_Closure_Graph, REQUEST_T, rule_subject,
                        rule_resource, rule_modality, rule_priority, rule_condition, lessSpecific, conRule, applicable,
                        notDomainSUB, notDomainRES, maxElem]
            with open(dir + os.sep + testName+"_MODEL2.txt", 'r') as f:
                modelContent = f.read()

            for formula in formulas:
                if re.search(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE) is not None:
                    matches = re.finditer(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE)
                    for matchNum, match in enumerate(matches, start=1):
                        dictOfFormulas[formula.name()] = modelContent[
                                                         match.start() + len(formula.name()) + 2:match.end() - 1:]
                else:
                    matches = re.finditer(r"%s=\[.*?\n\s*.*?\]" % formula.name(), modelContent, re.MULTILINE | re.DOTALL)
                    for matchNum, match in enumerate(matches, start=1):
                        dictOfFormulas[formula.name()] = modelContent[
                                                         match.start() + len(formula.name()) + 2:match.end() - 1:]

            q.add(eval(predicate_subject))
            q.add(eval(predicate_resource))
            q.add(eval(predicate_rule))
            q.add(eval(predicate_rule1))
            # q.add(eval(predicate_rule2))
            q.add(eval(predicate_context_distinct))
            q.add(eval(predicate_res1), eval(predicate_sub1))
            q.add(Distinct(permission, prohibition))
            q.add(eval(predicate_context))

            for formula in dictOfFormulas.keys():
                if formula == 'Subject_Graph':
                    predicate = eval(
                        dictOfFormulas['Subject_Graph'].replace('(Not(s', '(Not(auxSub1 == s').replace(', Not(s',
                                                                                                       ', Not(auxSub2 == s')
                    )
                    q.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                        Sub_Graph(auxSub1, auxSub2) == True,
                                                        Sub_Graph(auxSub1, auxSub2) == False)
                                 )
                          )
                if formula == 'Resources_Graph':
                    predicate = eval(
                        dictOfFormulas['Resources_Graph'].replace('(Not(r',
                                                                  '(Not(auxRes1 == r').replace(', Not(r',
                                                                                               ', Not(auxRes2 == r'))
                    q.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                        Res_Graph(auxRes1, auxRes2) == True,
                                                        Res_Graph(auxRes1, auxRes2) == False)
                                 )
                          )
                if formula == 'Transitive_Closure_Subject_Graph':
                    predicate = eval(
                        dictOfFormulas['Transitive_Closure_Subject_Graph'].replace('(Not(s',
                                                                                   '(Not(auxSub1 == s').replace(', Not(s',
                                                                                                                ', Not(auxSub2 == s')
                    )
                    q.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                        Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                                        Subject_Closure_Graph(auxSub1, auxSub2) == False)
                                 )
                          )
                if formula == 'Transitive_Closure_Resources_Graph':
                    predicate = eval(
                        dictOfFormulas['Transitive_Closure_Resources_Graph'].replace('(Not(r',
                                                                                     '(Not(auxRes1 == r').replace(', Not(r',
                                                                                                                  ', Not(auxRes2 == r'))
                    q.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                        Resource_Closure_Graph(auxRes1, auxRes2) == True,
                                                        Resource_Closure_Graph(auxRes1, auxRes2) == False)
                                 )
                          )
                if formula == 'REQUEST_T':
                    predicate = eval(
                        dictOfFormulas['REQUEST_T'].replace(', Not(r', ', Not(auxRes1 == r').replace('Not(s', 'Not(auxSub1 == s'))
                    q.add(ForAll([auxSub1, auxRes1], If(predicate,
                                                        REQUEST_T(auxSub1, auxRes1) == True,
                                                        REQUEST_T(auxSub1, auxRes1) == False)))

                if formula == 'rule_modality':
                    predicate = eval(
                        dictOfFormulas['rule_modality'].replace('Not(p', 'Not(auxModality == p').replace(
                            'Not(rule', 'Not(auxRule1 == rule'))
                    q.add(ForAll([auxRule1, auxModality], If(predicate,  # If it is this
                                                             rule_modality(auxRule1, auxModality) == True,  # Then True
                                                             rule_modality(auxRule1,
                                                                           auxModality) == False)))  # Else -> False)

                if formula == 'rule_subject':
                    predicate = eval(
                        dictOfFormulas['rule_subject'].replace(', Not(s', ', Not(auxSub1 == s').replace(
                            'Not(rule', 'Not(auxRule1 == rule'))
                    q.add(ForAll([auxRule1, auxSub1], If(predicate,  # If it is this
                                                         rule_subject(auxRule1, auxSub1) == True,  # Then True
                                                         rule_subject(auxRule1, auxSub1) == False)))  # Else -> False)

                if formula == 'rule_resource':
                    predicate = eval(
                        dictOfFormulas['rule_resource'].replace(', Not(r', ', Not(auxRes1 == r').replace(
                            'Not(rule', 'Not(auxRule1 == rule'))
                    q.add(ForAll([auxRule1, auxRes1], If(predicate,  # If it is this
                                                         rule_resource(auxRule1, auxRes1) == True,  # Then True
                                                         rule_resource(auxRule1, auxRes1) == False)))  # Else -> False)

                if formula == 'rule_condition':
                    predicate = eval(dictOfFormulas['rule_condition'].replace(
                        ', Not(c', ', Not(auxCon == c').replace('Not(rule', 'Not(auxRule1 == rule'))
                    q.add(ForAll([auxRule1, auxCon], If(predicate,  # If it is this
                                                        rule_condition(auxRule1, auxCon) == True,  # Then True
                                                        rule_condition(auxRule1, auxCon) == False)))  # Else -> False))

                if formula == 'rule_priority':
                    predicate = eval(dictOfFormulas['rule_priority'].replace(', Not(4', ', Not(auxInt == 4').replace(
                        ', Not(2', ', Not(auxInt == 2').replace(
                        ', Not(3', ', Not(auxInt == 3').replace(
                        ', Not(0', ', Not(auxInt == 0').replace(
                        ', Not(1', ', Not(auxInt == 1').replace('Not(rule', 'Not(auxRule1 == rule'))
                    q.add(ForAll([auxRule1, auxInt], If(predicate,  # If it is this
                                                        rule_priority(auxRule1, auxInt) == True,  # Then True
                                                        rule_priority(auxRule1, auxInt) == False)))  # Else -> False))

                if formula == 'lessSpecific':
                    predicate = eval(dictOfFormulas['lessSpecific'].replace(', r', ', auxRule2 == r').replace(
                        'And(r', 'And(auxRule1 == r'))
                    q.add(ForAll([auxRule1, auxRule2], If(predicate,
                                                          lessSpecific(auxRule1, auxRule2),
                                                          Not(lessSpecific(auxRule1, auxRule2)))))

                if formula == 'conRule':
                    predicate = eval(dictOfFormulas['conRule'].replace(', Not(r', ', Not(auxRule1 == r').replace(
                        'Not(c', 'Not(auxCon == c'))
                    q.add(ForAll([auxRule1, auxCon], If(predicate,
                                                        conRule(auxCon, auxRule1),
                                                        Not(conRule(auxCon, auxRule1)))))

                if formula == 'applicable':
                    predicate = eval(dictOfFormulas['applicable'].replace(
                        ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                 'And(auxSub1 == s'))
                    q.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                  applicable(auxSub1, auxRes1, auxRule1),
                                                                  Not(applicable(auxSub1, auxRes1, auxRule1)))))

                if formula == 'notDomainSub':
                    if "(s" in dictOfFormulas['notDomainSub']:
                        predicate = eval(dictOfFormulas['notDomainSub'].replace('(s', '(auxSub1 == s').replace(', s',
                                                                                                               ', auxSub1 == s'))
                    else:
                        predicate = eval(dictOfFormulas['notDomainSub'].replace('s', 'auxSub1 == s'))
                    q.add(ForAll([auxSub1], If(predicate,
                                               notDomainSUB(auxSub1),
                                               Not(notDomainSUB(auxSub1)))))

                if formula == 'notDomainRes':
                    if "(r" in dictOfFormulas['notDomainRes']:
                        predicate = eval(dictOfFormulas['notDomainRes'].replace('(r', '(auxRes1 == r').replace(', r',
                                                                                                               ', auxRes1 == r'))
                    else:
                        predicate = eval(dictOfFormulas['notDomainRes'].replace('r', 'auxRes1 == r'))
                    q.add(ForAll([auxRes1], If(predicate,
                                               notDomainRES(auxRes1),
                                               Not(notDomainRES(auxRes1)))))

                if formula == 'maxElem':
                    predicate = eval(dictOfFormulas['maxElem'].replace(
                        ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                 'And(auxSub1 == s'))
                    q.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                  maxElem(auxSub1, auxRes1, auxRule1),
                                                                  Not(maxElem(auxSub1, auxRes1, auxRule1)))))

                isPrecededBy = Function('isPrecededBy', V_SUB, V_RES, rules, rules, BoolSort())
                auxRule1, auxRule2, auxRule3 = Consts('auxRule1 auxRule2 auxRule3', rules)
                auxRes1 = Const('auxRes1', V_RES)
                auxSub1 = Const('auxSub1', V_SUB)
                q.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],
                             Implies(And(REQUEST_T(auxSub1, auxRes1),
                                         applicable(auxSub1, auxRes1, auxRule1),
                                         applicable(auxSub1, auxRes1, auxRule2),
                                         auxRule1 != auxRule2,
                                         Or(lessSpecific(auxRule1, auxRule2),
                                            And(maxElem(auxSub1, auxRes1, auxRule1),
                                                maxElem(auxSub1, auxRes1, auxRule2),
                                                rule_modality(auxRule1, permission),
                                                rule_modality(auxRule2, prohibition)
                                                )
                                            )
                                         ),
                                     isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)
                                     )
                             )
                      )
                q.add(Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                              And(REQUEST_T(auxSub1, auxRes1),
                                  applicable(auxSub1, auxRes1, auxRule1),
                                  applicable(auxSub1, auxRes1, auxRule2),
                                  auxRule1 != auxRule2,
                                  Or(lessSpecific(auxRule1, auxRule2),
                                     And(maxElem(auxSub1, auxRes1, auxRule1),
                                         maxElem(auxSub1, auxRes1, auxRule2),
                                         rule_modality(auxRule1, permission),
                                         rule_modality(auxRule2, prohibition)
                                         )
                                     )
                                  )
                              )
                      )

            #t3 = time.time()
            #print("Time to start the third check:", t3 - ts)
            print(q.check())
            #t4 = time.time()
            #print("Time to finish the third check", t4 - t3)
            if q.check() == sat:
                f = open(dir + os.sep + testName+"_MODEL3.txt", "w+")
                for variable in q.model():
                    f.write(str(variable)), f.write("="), f.write(str(q.model()[variable])), f.write("\n")
                f.close()

                dictOfSubstitutions = dict()
                chosenVariables = [permission, prohibition]
                for sub in Python_Sub_Graph.keys():
                    chosenVariables.append(sub)
                for res in Python_Res_Graph.keys():
                    chosenVariables.append(res)
                for key in Python_Rules_Text_Dict.keys():
                    chosenVariables.append(eval(key))
                for context in Python_Context_List:
                    chosenVariables.append(eval(context))

                # Rewriting the variables
                for variable in chosenVariables:
                    with open(dir + os.sep + testName+"_MODEL3.txt") as f:
                        for line in f:
                            matches = re.finditer(r"^" + str(variable) + "=", line)
                            for matchNum, match in enumerate(matches):
                                dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
                    f.close()

                with open(dir + os.sep + testName+"_MODEL3.txt", 'r') as f:
                    modelContent = f.read()
                f.close()
                for key in dictOfSubstitutions.keys():
                    modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0, re.MULTILINE)
                # Erasing the k!#### and replacing for the variables
                modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
                # Erasing k!#### variables
                modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
                # Erasing weird syntax from the solver (If(Var(0) == ...)
                modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "",
                                      modelContent)
                modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
                modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
                # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
                modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
                modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
                modelContent = re.sub(r"\[ Or", "[Or", modelContent)
                f = open(dir + os.sep + testName+"_MODEL3.txt", "w+")
                f.write(modelContent)
                f.close()

                # Rewriting the model for rerun in another Z3 model and accomplish the Exists quantification
                # Adding a new solver
                u = Solver()
                dictOfFormulas = dict()

                formulas = [Sub_Graph, Subject_Closure_Graph, Res_Graph, Resource_Closure_Graph, REQUEST_T,
                            rule_subject,
                            rule_resource, rule_modality, rule_priority, rule_condition, lessSpecific, conRule,
                            applicable,
                            notDomainSUB, notDomainRES, maxElem, isPrecededBy]
                with open(dir + os.sep + testName+"_MODEL3.txt", 'r') as f:
                    modelContent = f.read()

                for formula in formulas:
                    if re.search(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE) is not None:
                        matches = re.finditer(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE)
                        for matchNum, match in enumerate(matches, start=1):
                            dictOfFormulas[formula.name()] = modelContent[
                                                             match.start() + len(formula.name()) + 2:match.end() - 1:]
                    else:
                        matches = re.finditer(r"%s=\[.*?\n\s*.*?\]" % formula.name(), modelContent,
                                              re.MULTILINE | re.DOTALL)
                        for matchNum, match in enumerate(matches, start=1):
                            dictOfFormulas[formula.name()] = modelContent[
                                                             match.start() + len(formula.name()) + 2:match.end() - 1:]

                u.add(eval(predicate_subject))
                u.add(eval(predicate_resource))
                u.add(eval(predicate_rule))
                u.add(eval(predicate_rule1))
                # u.add(eval(predicate_rule2))
                u.add(eval(predicate_context_distinct))
                u.add(eval(predicate_res1), eval(predicate_sub1))
                u.add(Distinct(permission, prohibition))
                u.add(eval(predicate_context))

                for formula in dictOfFormulas.keys():
                    if formula == 'Subject_Graph':
                        predicate = eval(
                            dictOfFormulas['Subject_Graph'].replace('(Not(s', '(Not(auxSub1 == s').replace(', Not(s',
                                                                                                           ', Not(auxSub2 == s')
                        )
                        u.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                            Sub_Graph(auxSub1, auxSub2) == True,
                                                            Sub_Graph(auxSub1, auxSub2) == False)
                                     )
                              )
                    if formula == 'Resources_Graph':
                        predicate = eval(
                            dictOfFormulas['Resources_Graph'].replace('(Not(r',
                                                                      '(Not(auxRes1 == r').replace(', Not(r',
                                                                                                   ', Not(auxRes2 == r'))
                        u.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                            Res_Graph(auxRes1, auxRes2) == True,
                                                            Res_Graph(auxRes1, auxRes2) == False)
                                     )
                              )
                    if formula == 'Transitive_Closure_Subject_Graph':
                        predicate = eval(
                            dictOfFormulas['Transitive_Closure_Subject_Graph'].replace('(Not(s',
                                                                                       '(Not(auxSub1 == s').replace(
                                ', Not(s',
                                ', Not(auxSub2 == s')
                        )
                        u.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                            Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                                            Subject_Closure_Graph(auxSub1, auxSub2) == False)
                                     )
                              )
                    if formula == 'Transitive_Closure_Resources_Graph':
                        predicate = eval(
                            dictOfFormulas['Transitive_Closure_Resources_Graph'].replace('(Not(r',
                                                                                         '(Not(auxRes1 == r').replace(
                                ', Not(r',
                                ', Not(auxRes2 == r'))
                        u.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                            Resource_Closure_Graph(auxRes1, auxRes2) == True,
                                                            Resource_Closure_Graph(auxRes1, auxRes2) == False)
                                     )
                              )
                    if formula == 'REQUEST_T':
                        predicate = eval(
                            dictOfFormulas['REQUEST_T'].replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                 'And(auxSub1 == s'))
                        u.add(ForAll([auxSub1, auxRes1], If(predicate,
                                                            REQUEST_T(auxSub1, auxRes1) == True,
                                                            REQUEST_T(auxSub1, auxRes1) == False)))

                    if formula == 'rule_modality':
                        predicate = eval(
                            dictOfFormulas['rule_modality'].replace(', p', ', auxModality == p').replace(
                                'And(rule', 'And(auxRule1 == rule'))
                        u.add(ForAll([auxRule1, auxModality], If(predicate,  # If it is this
                                                                 rule_modality(auxRule1, auxModality) == True,
                                                                 # Then True
                                                                 rule_modality(auxRule1,
                                                                               auxModality) == False)))  # Else -> False)

                    if formula == 'rule_subject':
                        predicate = eval(
                            dictOfFormulas['rule_subject'].replace(', Not(s', ', Not(auxSub1 == s').replace(
                                'Not(rule', 'Not(auxRule1 == rule'))
                        u.add(ForAll([auxRule1, auxSub1], If(predicate,  # If it is this
                                                             rule_subject(auxRule1, auxSub1) == True,  # Then True
                                                             rule_subject(auxRule1,
                                                                          auxSub1) == False)))  # Else -> False)

                    if formula == 'rule_resource':
                        predicate = eval(
                            dictOfFormulas['rule_resource'].replace(', Not(r', ', Not(auxRes1 == r').replace(
                                'Not(rule', 'Not(auxRule1 == rule'))
                        u.add(ForAll([auxRule1, auxRes1], If(predicate,  # If it is this
                                                             rule_resource(auxRule1, auxRes1) == True,  # Then True
                                                             rule_resource(auxRule1,
                                                                           auxRes1) == False)))  # Else -> False)

                    if formula == 'rule_condition':
                        predicate = eval(dictOfFormulas['rule_condition'].replace(
                            ', Not(c', ', Not(auxCon == c').replace('Not(rule', 'Not(auxRule1 == rule'))
                        u.add(ForAll([auxRule1, auxCon], If(predicate,  # If it is this
                                                            rule_condition(auxRule1, auxCon) == True,  # Then True
                                                            rule_condition(auxRule1,
                                                                           auxCon) == False)))  # Else -> False))

                    if formula == 'rule_priority':
                        predicate = eval(
                            dictOfFormulas['rule_priority'].replace(', Not(4', ', Not(auxInt == 4').replace(
                                ', Not(2', ', Not(auxInt == 2').replace(
                                ', Not(3', ', Not(auxInt == 3').replace(
                                ', Not(0', ', Not(auxInt == 0').replace(
                                ', Not(1', ', Not(auxInt == 1').replace('Not(rule', 'Not(auxRule1 == rule'))
                        u.add(ForAll([auxRule1, auxInt], If(predicate,  # If it is this
                                                            rule_priority(auxRule1, auxInt) == True,  # Then True
                                                            rule_priority(auxRule1,
                                                                          auxInt) == False)))  # Else -> False))

                    if formula == 'lessSpecific':
                        predicate = eval(dictOfFormulas['lessSpecific'].replace(', r', ', auxRule2 == r').replace(
                            'And(r', 'And(auxRule1 == r'))
                        u.add(ForAll([auxRule1, auxRule2], If(predicate,
                                                              lessSpecific(auxRule1, auxRule2),
                                                              Not(lessSpecific(auxRule1, auxRule2)))))

                    if formula == 'conRule':
                        predicate = eval(dictOfFormulas['conRule'].replace(', Not(r', ', Not(auxRule1 == r').replace(
                            '(Not(c', '(Not(auxCon == c'))
                        u.add(ForAll([auxRule1, auxCon], If(predicate,
                                                            conRule(auxCon, auxRule1),
                                                            Not(conRule(auxCon, auxRule1)))))

                    if formula == 'applicable':
                        predicate = eval(dictOfFormulas['applicable'].replace(
                            ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                     'And(auxSub1 == s'))
                        u.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                      applicable(auxSub1, auxRes1, auxRule1),
                                                                      Not(applicable(auxSub1, auxRes1, auxRule1)))))

                    if formula == 'notDomainSub':
                        if "(s" in dictOfFormulas['notDomainSub']:
                            predicate = eval(dictOfFormulas['notDomainSub'].replace('(s', '(auxSub1 == s').replace(', s',
                                                                                                                   ', auxSub1 == s'))
                        else:
                            predicate = eval(dictOfFormulas['notDomainSub'].replace('s', 'auxSub1 == s'))
                        u.add(ForAll([auxSub1], If(predicate,
                                                   notDomainSUB(auxSub1),
                                                   Not(notDomainSUB(auxSub1)))))

                    if formula == 'notDomainRes':
                        if "(r" in dictOfFormulas['notDomainRes']:
                            predicate = eval(dictOfFormulas['notDomainRes'].replace('(r', '(auxRes1 == r').replace(', r',
                                                                                                               ', auxRes1 == r'))
                        else:
                            predicate = eval(dictOfFormulas['notDomainRes'].replace('r', 'auxRes1 == r'))
                        u.add(ForAll([auxRes1], If(predicate,
                                                   notDomainRES(auxRes1),
                                                   Not(notDomainRES(auxRes1)))))

                    if formula == 'maxElem':
                        predicate = eval(dictOfFormulas['maxElem'].replace(
                            ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                     'And(auxSub1 == s'))
                        u.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                      maxElem(auxSub1, auxRes1, auxRule1),
                                                                      Not(maxElem(auxSub1, auxRes1, auxRule1)))))

                    if formula == 'isPrecededBy':
                        dictOfFormulas['isPrecededBy'] = dictOfFormulas['isPrecededBy'].replace(', rule', ', auxRule1 == rule').replace(
                            'And(s', 'And(auxSub1 == s').replace(', r', ', auxRes1 == r')
                        matches = re.finditer(r"auxRule1", dictOfFormulas['isPrecededBy'], re.MULTILINE)

                        for matchNum, match in enumerate(matches, start=1):
                            if matchNum % 2 == 0:
                                dictOfFormulas['isPrecededBy'] = list(dictOfFormulas['isPrecededBy'])
                                dictOfFormulas['isPrecededBy'][match.end()-1] = '2'
                                dictOfFormulas['isPrecededBy'] = "".join(dictOfFormulas['isPrecededBy'])

                        predicate = eval(dictOfFormulas['isPrecededBy'])
                        u.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],
                                     If(predicate,
                                        isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                                        Not(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)))))

                    pseudoSink = Function('pseudoSink', V_SUB, V_RES, CONTEXT, rules, BoolSort())
                    auxRes1 = Const('auxRes1', V_RES)
                    auxSub1 = Const('auxSub1', V_SUB)
                    auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
                    auxCon = Const('auxCon', CONTEXT)
                    u.add(ForAll([auxSub1, auxRes1, auxCon, auxRule1],
                                 If(And(applicable(auxSub1, auxRes1, auxRule1),
                                        conRule(auxCon, auxRule1),
                                        ForAll([auxRule2],
                                               Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                                                       Not(conRule(auxCon, auxRule2))))),
                                    pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                    Not(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1))
                                    )
                                 )
                          )
                    u.add(Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                  And(applicable(auxSub1, auxRes1, auxRule1),
                                      conRule(auxCon, auxRule1),
                                      ForAll([auxRule2],
                                             Implies(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                                                     Not(conRule(auxCon, auxRule2)))))
                                  )
                          )

                #t3 = time.time()
                #print("Time to start the fourth check:", t3 - ts)
                print(u.check())
                #t4 = time.time()
                #print("Time to finish the fourth check", t4 - t3)
                if u.check() == sat:
                    f = open(dir + os.sep + testName+"_MODEL4.txt", "w+")
                    for variable in u.model():
                        f.write(str(variable)), f.write("="), f.write(str(u.model()[variable])), f.write("\n")
                    f.close()

                    dictOfSubstitutions = dict()

                    # Rewriting the variables
                    for variable in chosenVariables:
                        with open(dir + os.sep + testName+"_MODEL4.txt") as f:
                            for line in f:
                                matches = re.finditer(r"^" + str(variable) + "=", line)
                                for matchNum, match in enumerate(matches):
                                    dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
                        f.close()

                    with open(dir + os.sep + testName+"_MODEL4.txt", 'r') as f:
                        modelContent = f.read()
                    f.close()
                    for key in dictOfSubstitutions.keys():
                        modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0, re.MULTILINE)
                    # Erasing the k!#### and replacing for the variables
                    modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
                    # Erasing k!#### variables
                    modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
                    # Erasing weird syntax from the solver (If(Var(0) == ...)
                    modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "",
                                          modelContent)
                    modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
                    modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
                    # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
                    modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
                    modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
                    modelContent = re.sub(r"\[ Or", "[Or", modelContent)
                    f = open(dir + os.sep + testName+"_MODEL4.txt", "w+")
                    f.write(modelContent)
                    f.close()

                    # Rewriting the model for rerun in another Z3 model and accomplish the Exists quantification
                    # Adding a new solver
                    v = Solver()
                    dictOfFormulas = dict()

                    formulas = [Sub_Graph, Subject_Closure_Graph, Res_Graph, Resource_Closure_Graph, REQUEST_T,
                                rule_subject,
                                rule_resource, rule_modality, rule_priority, rule_condition, lessSpecific, conRule,
                                applicable,
                                notDomainSUB, notDomainRES, maxElem, isPrecededBy, pseudoSink]
                    with open(dir + os.sep + testName+"_MODEL4.txt", 'r') as f:
                        modelContent = f.read()

                    for formula in formulas:
                        if re.search(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE) is not None:
                            matches = re.finditer(r"%s=\[.*?\s*.*?\]" % formula.name(), modelContent, re.MULTILINE)
                            for matchNum, match in enumerate(matches, start=1):
                                dictOfFormulas[formula.name()] = modelContent[
                                                                 match.start() + len(formula.name()) + 2:match.end() - 1:]
                        else:
                            matches = re.finditer(r"%s=\[.*?\n\s*.*?\]" % formula.name(), modelContent,
                                                  re.MULTILINE | re.DOTALL)
                            for matchNum, match in enumerate(matches, start=1):
                                dictOfFormulas[formula.name()] = modelContent[
                                                                 match.start() + len(formula.name()) + 2:match.end() - 1:]

                    v.add(eval(predicate_subject))
                    v.add(eval(predicate_resource))
                    v.add(eval(predicate_rule))
                    v.add(eval(predicate_rule1))
                    # u.add(eval(predicate_rule2))
                    v.add(eval(predicate_context_distinct))
                    v.add(eval(predicate_res1), eval(predicate_sub1))
                    v.add(Distinct(permission, prohibition))
                    v.add(eval(predicate_context))

                    for formula in dictOfFormulas.keys():
                        if formula == 'Subject_Graph':
                            predicate = eval(
                                dictOfFormulas['Subject_Graph'].replace('(Not(s', '(Not(auxSub1 == s').replace(', Not(s',
                                                                                                               ', Not(auxSub2 == s')
                            )
                            v.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                                Sub_Graph(auxSub1, auxSub2) == True,
                                                                Sub_Graph(auxSub1, auxSub2) == False)
                                         )
                                  )
                        if formula == 'Resources_Graph':
                            predicate = eval(
                                dictOfFormulas['Resources_Graph'].replace('(Not(r',
                                                                          '(Not(auxRes1 == r').replace(', Not(r',
                                                                                                       ', Not(auxRes2 == r'))
                            v.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                                Res_Graph(auxRes1, auxRes2) == True,
                                                                Res_Graph(auxRes1, auxRes2) == False)
                                         )
                                  )
                        if formula == 'Transitive_Closure_Subject_Graph':
                            predicate = eval(
                                dictOfFormulas['Transitive_Closure_Subject_Graph'].replace('(Not(s',
                                                                                           '(Not(auxSub1 == s').replace(
                                    ', Not(s',
                                    ', Not(auxSub2 == s')
                            )
                            v.add(ForAll([auxSub1, auxSub2], If(predicate,
                                                                Subject_Closure_Graph(auxSub1, auxSub2) == True,
                                                                Subject_Closure_Graph(auxSub1, auxSub2) == False)
                                         )
                                  )
                        if formula == 'Transitive_Closure_Resources_Graph':
                            predicate = eval(
                                dictOfFormulas['Transitive_Closure_Resources_Graph'].replace('(Not(r',
                                                                                             '(Not(auxRes1 == r').replace(
                                    ', Not(r',
                                    ', Not(auxRes2 == r'))
                            v.add(ForAll([auxRes1, auxRes2], If(predicate,
                                                                Resource_Closure_Graph(auxRes1, auxRes2) == True,
                                                                Resource_Closure_Graph(auxRes1, auxRes2) == False)
                                         )
                                  )
                        if formula == 'REQUEST_T':
                            predicate = eval(
                                dictOfFormulas['REQUEST_T'].replace(', Not(r', ', Not(auxRes1 == r').replace('Not(s',
                                                                                                             'Not(auxSub1 == s'))
                            v.add(ForAll([auxSub1, auxRes1], If(predicate,
                                                                REQUEST_T(auxSub1, auxRes1) == True,
                                                                REQUEST_T(auxSub1, auxRes1) == False)))

                        if formula == 'rule_modality':
                            predicate = eval(
                                dictOfFormulas['rule_modality'].replace(', Not(p', ', Not(auxModality == p').replace(
                                    'Not(rule', 'Not(auxRule1 == rule'))
                            v.add(ForAll([auxRule1, auxModality], If(predicate,  # If it is this
                                                                     rule_modality(auxRule1, auxModality) == True,
                                                                     # Then True
                                                                     rule_modality(auxRule1,
                                                                                   auxModality) == False)))  # Else -> False)

                        if formula == 'rule_subject':
                            predicate = eval(
                                dictOfFormulas['rule_subject'].replace(', Not(s', ', Not(auxSub1 == s').replace(
                                    'Not(rule', 'Not(auxRule1 == rule'))
                            v.add(ForAll([auxRule1, auxSub1], If(predicate,  # If it is this
                                                                 rule_subject(auxRule1, auxSub1) == True,  # Then True
                                                                 rule_subject(auxRule1,
                                                                              auxSub1) == False)))  # Else -> False)

                        if formula == 'rule_resource':
                            predicate = eval(
                                dictOfFormulas['rule_resource'].replace(', Not(r', ', Not(auxRes1 == r').replace(
                                    'Not(rule', 'Not(auxRule1 == rule'))
                            v.add(ForAll([auxRule1, auxRes1], If(predicate,  # If it is this
                                                                 rule_resource(auxRule1, auxRes1) == True,  # Then True
                                                                 rule_resource(auxRule1,
                                                                               auxRes1) == False)))  # Else -> False)

                        if formula == 'rule_condition':
                            predicate = eval(dictOfFormulas['rule_condition'].replace(
                                ', Not(c', ', Not(auxCon == c').replace('Not(rule', 'Not(auxRule1 == rule'))
                            v.add(ForAll([auxRule1, auxCon], If(predicate,  # If it is this
                                                                rule_condition(auxRule1, auxCon) == True,  # Then True
                                                                rule_condition(auxRule1,
                                                                               auxCon) == False)))  # Else -> False))

                        if formula == 'rule_priority':
                            predicate = eval(
                                dictOfFormulas['rule_priority'].replace(', Not(4', ', Not(auxInt == 4').replace(
                                    ', Not(2', ', Not(auxInt == 2').replace(
                                    ', Not(3', ', Not(auxInt == 3').replace(
                                    ', Not(0', ', Not(auxInt == 0').replace(
                                    ', Not(1', ', Not(auxInt == 1').replace('Not(rule', 'Not(auxRule1 == rule'))
                            v.add(ForAll([auxRule1, auxInt], If(predicate,  # If it is this
                                                                rule_priority(auxRule1, auxInt) == True,  # Then True
                                                                rule_priority(auxRule1,
                                                                              auxInt) == False)))  # Else -> False))

                        if formula == 'lessSpecific':
                            predicate = eval(
                                dictOfFormulas['lessSpecific'].replace(', Not(r', ', Not(auxRule2 == r').replace(
                                    'Not(r', 'Not(auxRule1 == r'))
                            v.add(ForAll([auxRule1, auxRule2], If(predicate,
                                                                  lessSpecific(auxRule1, auxRule2),
                                                                  Not(lessSpecific(auxRule1, auxRule2)))))

                        if formula == 'conRule':
                            predicate = eval(dictOfFormulas['conRule'].replace(', r', ', auxRule1 == r').replace(
                                'c', 'auxCon == c'))
                            v.add(ForAll([auxRule1, auxCon], If(predicate,
                                                                conRule(auxCon, auxRule1),
                                                                Not(conRule(auxCon, auxRule1)))))

                        if formula == 'applicable':
                            predicate = eval(dictOfFormulas['applicable'].replace(
                                ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace('And(s',
                                                                                                         'And(auxSub1 == s'))
                            v.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                          applicable(auxSub1, auxRes1, auxRule1),
                                                                          Not(applicable(auxSub1, auxRes1, auxRule1)))))

                        if formula == 'notDomainSub':
                            if "(s" in dictOfFormulas['notDomainSub']:
                                predicate = eval(
                                    dictOfFormulas['notDomainSub'].replace('(s', '(auxSub1 == s').replace(', s',
                                                                                                          ', auxSub1 == s'))
                            else:
                                predicate = eval(dictOfFormulas['notDomainSub'].replace('s', 'auxSub1 == s'))
                            v.add(ForAll([auxSub1], If(predicate,
                                                       notDomainSUB(auxSub1),
                                                       Not(notDomainSUB(auxSub1)))))

                        if formula == 'notDomainRes':
                            if "(r" in dictOfFormulas['notDomainRes']:
                                predicate = eval(
                                    dictOfFormulas['notDomainRes'].replace('(r', '(auxRes1 == r').replace(', r',
                                                                                                          ', auxRes1 == r'))
                            else:
                                predicate = eval(dictOfFormulas['notDomainRes'].replace('r', 'auxRes1 == r'))
                            v.add(ForAll([auxRes1], If(predicate,
                                                       notDomainRES(auxRes1),
                                                       Not(notDomainRES(auxRes1)))))

                        if formula == 'maxElem':
                            predicate = eval(dictOfFormulas['maxElem'].replace(
                                ', Not(rule', ', Not(auxRule1 == rule').replace(', Not(r', ', Not(auxRes1 == r').replace(
                                'Not(s',
                                'Not(auxSub1 == s'))
                            v.add(ForAll([auxRule1, auxSub1, auxRes1], If(predicate,
                                                                          maxElem(auxSub1, auxRes1, auxRule1),
                                                                          Not(maxElem(auxSub1, auxRes1, auxRule1)))))

                        if formula == 'isPrecededBy':
                            dictOfFormulas['isPrecededBy'] = dictOfFormulas['isPrecededBy'].replace(', rule',
                                                                                                    ', auxRule1 == rule').replace(
                                'And(s', 'And(auxSub1 == s').replace(', r', ', auxRes1 == r')

                            matches = re.finditer(r"auxRule1", dictOfFormulas['isPrecededBy'], re.MULTILINE)

                            for matchNum, match in enumerate(matches, start=1):
                                if matchNum % 2 == 0:
                                    dictOfFormulas['isPrecededBy'] = list(dictOfFormulas['isPrecededBy'])
                                    dictOfFormulas['isPrecededBy'][match.end() - 1] = '2'
                                    dictOfFormulas['isPrecededBy'] = "".join(dictOfFormulas['isPrecededBy'])

                            predicate = eval(dictOfFormulas['isPrecededBy'])
                            v.add(ForAll([auxSub1, auxRes1, auxRule1, auxRule2],
                                         If(predicate,
                                            isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2),
                                            Not(isPrecededBy(auxSub1, auxRes1, auxRule1, auxRule2)))))

                        if formula == 'pseudoSink':
                            predicate = eval(dictOfFormulas['pseudoSink'].replace('And(s', 'And(auxSub1 == s').replace(
                                ', rule', ', auxRule1 == rule').replace(', r', ', auxRes1 == r').replace(', c',
                                                                                                         ', auxCon == c'))
                            v.add(ForAll([auxSub1, auxRes1, auxCon, auxRule1],
                                         If(predicate,
                                            pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                            Not(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1)))))

                        # Declaring the four properties
                        accessibility = Function('Accessibility', V_SUB, V_RES, CONTEXT, BoolSort())
                        auxRes1 = Const('auxRes1', V_RES)
                        auxSub1 = Const('auxSub1', V_SUB)
                        auxRule1 = Const('auxRule1', rules)
                        auxCon = Const('auxCon', CONTEXT)
                        v.add(ForAll([auxSub1, auxRes1, auxCon],
                                     If(And(ForAll([auxRule1], Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                                                       rule_modality(auxRule1, permission)
                                                                       )
                                                   ),
                                            Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon, auxRule1))
                                            ),
                                        accessibility(auxSub1, auxRes1, auxCon),
                                        Not(accessibility(auxSub1, auxRes1, auxCon))
                                        )
                                     )
                              )

                        # xx, yy = Ints("xx yy")
                        # condition0, condition1, condition2 = Bools("c0 c1 c2")
                        # condition0 = xx > 0
                        # condition1 = xx > yy
                        # condition2 = yy == 10
                        #
                        # linkingContextAndConditions = Function('LinkingContextAndConditions', CONTEXT, BoolSort(),
                        #                                        BoolSort())
                        # auxCondition = Const('auxCondition', BoolSort())

                        # linkingContextAndConditions(c0, condition0), linkingContextAndConditions(c1, condition1),
                        # linkingContextAndConditions(c2, condition2))
                        # s.add(ForAll([auxCon, auxCondition], If(Or(And(auxCon == c0, auxCondition == condition0),
                        #                                            And(auxCon == c1, auxCondition == condition1),
                        #                                            And(auxCon == c2, auxCondition == condition2)),
                        #                                         linkingContextAndConditions(auxCon, auxCondition),
                        #                                         Not(linkingContextAndConditions(auxCon, auxCondition)
                        #                                             )
                        #                                         )
                        #              )
                        #       )

                        # accessibilityWithConditions = Function('AccessibilityWithConditions', V_SUB, V_RES, CONTEXT,
                        #                                        BoolSort())
                        # auxRes1 = Const('auxRes1', V_RES)
                        # auxSub1 = Const('auxSub1', V_SUB)
                        # auxRule1 = Const('auxRule1', rules)
                        # auxCon = Const('auxCon', CONTEXT)
                        # auxCondition = Const('auxCondition', BoolSort())
                        # s.add(ForAll([auxSub1, auxRes1, auxCon],
                        #              If(And(ForAll([auxRule1], Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                        #                                                rule_modality(auxRule1, permission)
                        #                                                )
                        #                            ),
                        #                     Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon, auxRule1)),
                        #                     ForAll(auxCondition, Implies(linkingContextAndConditions(auxCon, auxCondition),
                        #                                                  auxCondition))
                        #                     ),
                        #                 accessibilityWithConditions(auxSub1, auxRes1, auxCon),
                        #                 Not(accessibilityWithConditions(auxSub1, auxRes1, auxCon))
                        #                 )
                        #              )
                        #       )

                        hiddenDocument = Function('HiddenDocument', CONTEXT, BoolSort())
                        auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
                        auxSub1 = Const('auxSub1', V_SUB)
                        auxCon = Const('auxCon', CONTEXT)
                        auxRule1 = Const('auxRule1', rules)
                        v.add(ForAll(auxCon,
                                     If(Exists(auxRes1,
                                               And(notDomainRES(auxRes1),
                                                   ForAll([auxSub1],
                                                          Implies(REQUEST_T(auxSub1, auxRes1),
                                                                  Not(And(ForAll(auxRule1,
                                                                                 Implies(pseudoSink(auxSub1, auxRes1,
                                                                                                    auxCon, auxRule1),
                                                                                         rule_modality(auxRule1, permission)
                                                                                         )
                                                                                 ),
                                                                          Exists(auxRule1,
                                                                                 pseudoSink(auxSub1, auxRes1, auxCon,
                                                                                            auxRule1)))
                                                                      )
                                                                  )
                                                          )
                                                   )
                                               ),
                                        hiddenDocument(auxCon),
                                        Not(hiddenDocument(auxCon)
                                            )
                                        )
                                     )
                              )

                        hiddenDataSet = Function('hiddenDataSet', CONTEXT, V_RES, BoolSort())
                        auxRes1, auxRes2 = Consts('auxRes1 auxRes2', V_RES)
                        auxSub1 = Const('auxSub1', V_SUB)
                        auxCon = Const('auxCon', CONTEXT)
                        auxRule1 = Const('auxRule1', rules)
                        v.add(ForAll([auxCon, auxRes1],
                                     If(And(notDomainRES(auxRes1),
                                            ForAll([auxSub1, auxRes2],
                                                   Implies(And(REQUEST_T(auxSub1, auxRes2),
                                                               auxRes2 == auxRes1),
                                                           Not(And(ForAll(auxRule1,
                                                                          Implies(pseudoSink(auxSub1, auxRes1, auxCon,
                                                                                             auxRule1),
                                                                                  rule_modality(auxRule1, permission))),
                                                                   Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon,
                                                                                               auxRule1))))))),
                                        hiddenDataSet(auxCon, auxRes1),
                                        Not(hiddenDataSet(auxCon, auxRes1))
                                        )
                                     )
                              )

                        UnavailableDocument = Bool('UnavailableDocument')
                        v.add(Implies(Exists(auxRes1, ForAll([auxCon], hiddenDataSet(auxCon, auxRes1))),
                                      UnavailableDocument))
                        v.add(Implies(UnavailableDocument,
                                      Exists(auxRes1, ForAll([auxCon], hiddenDataSet(auxCon, auxRes1)))))

                        gratingContext = Function('gratingContext', V_SUB, V_RES, CONTEXT, BoolSort())
                        auxRes1 = Const('auxRes1', V_RES)
                        auxSub1 = Const('auxSub1', V_SUB)
                        auxRule1 = Const('auxRule1', rules)
                        auxCon = Const('auxCon', CONTEXT)
                        v.add(ForAll([auxSub1, auxRes1, auxCon],
                                     If(And(ForAll([auxRule1], Implies(pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                                                       rule_modality(auxRule1, permission)
                                                                       )
                                                   ),
                                            Exists(auxRule1, pseudoSink(auxSub1, auxRes1, auxCon, auxRule1))
                                            ),
                                        gratingContext(auxSub1, auxRes1, auxCon),
                                        Not(gratingContext(auxSub1, auxRes1, auxCon))
                                        )
                                     )
                              )

                        ineffectiveSet = Function('ineffectiveSet', rules, BoolSort())
                        auxRes1 = Const('auxRes1', V_RES)
                        auxSub1 = Const('auxSub1', V_SUB)
                        auxRule1, auxRule2 = Consts('auxRule1 auxRule2', rules)
                        auxCon = Const('auxCon', CONTEXT)
                        v.add(ForAll([auxRule1],
                                     If(Not(Exists([auxSub1, auxRes1, auxCon],
                                                   And(REQUEST_T(auxSub1, auxRes1),
                                                       conRule(auxCon, auxRule1),
                                                       pseudoSink(auxSub1, auxRes1, auxCon, auxRule1),
                                                       Or(Not(Exists(auxRule2, And(pseudoSink(auxSub1, auxRes1, auxCon,
                                                                                              auxRule2),
                                                                                   auxRule1 != auxRule2))),
                                                          And(rule_modality(auxRule1, prohibition),
                                                              ForAll(auxRule2, Implies(And(pseudoSink(auxSub1, auxRes1,
                                                                                                      auxCon, auxRule2),
                                                                                           auxRule1 != auxRule2),
                                                                                       rule_modality(auxRule2, permission)))
                                                              )
                                                          )))),
                                        ineffectiveSet(auxRule1),
                                        Not(ineffectiveSet(auxRule1))
                                        )
                                     )
                              )

                    #t3 = time.time()
                    #print("Time to start the fifth check:", t3 - ts)
                    print(v.check())
                    #t4 = time.time()
                    #print("Time to finish the fifth check", t4 - t3)
                    if v.check() == sat:
                        f = open(dir + os.sep + testName+"_MODEL5.txt", "w+")
                        for variable in v.model():
                            f.write(str(variable)), f.write("="), f.write(str(v.model()[variable])), f.write("\n")
                        f.close()

                        dictOfSubstitutions = dict()

                        # Rewriting the variables
                        for variable in chosenVariables:
                            with open(dir + os.sep + testName+"_MODEL5.txt") as f:
                                for line in f:
                                    matches = re.finditer(r"^" + str(variable) + "=", line)
                                    for matchNum, match in enumerate(matches):
                                        dictOfSubstitutions[variable] = line[match.end():len(line) - 1:]
                            f.close()

                        with open(dir + os.sep + testName+"_MODEL5.txt", 'r') as f:
                            modelContent = f.read()
                        f.close()
                        for key in dictOfSubstitutions.keys():
                            modelContent = re.sub(r"\b%s\b" % dictOfSubstitutions[key], str(key), modelContent, 0,
                                                  re.MULTILINE)
                        # Erasing the k!#### and replacing for the variables
                        modelContent = re.sub(r"(k![0-9]+\(Var\([0-9]\)\)) == ", "", modelContent)
                        # Erasing k!#### variables
                        modelContent = re.sub(r"k![0-9]+=(.*?)\n", "", modelContent)
                        # Erasing weird syntax from the solver (If(Var(0) == ...)
                        modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, [0-9a-zA-Z!]+\)+ == ", "",
                                              modelContent)
                        modelContent = re.sub(r"If\(Var\([0-9]\) == [0-9a-zA-Z!]+, [0-9a-zA-Z!]+, ", "", modelContent)
                        modelContent = re.sub(r"Var\([0-9]\) == ", "", modelContent)
                        # modelContent = re.sub(r"\[(.*?)else ->[ \n]", "[", modelContent)
                        modelContent = re.sub(r"\[else ->[ \n]", "[", modelContent)
                        modelContent = re.sub(r"\[.*?else ->", "[", modelContent)
                        modelContent = re.sub(r"\[ Or", "[Or", modelContent)
                        f = open(dir + os.sep + testName+"_MODEL5.txt", "w+")
                        f.write(modelContent)
                        f.close()

    #print("Time to finish all the SGAC check:", time.time()-ts)
