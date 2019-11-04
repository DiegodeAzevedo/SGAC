import random
import set_functions

Python_Sub_Graph = dict()
Python_Res_Graph = dict()
Python_Sub_Closure_Graph = dict()
Python_Res_Closure_Graph = dict()
Python_Rules = dict()
Python_Context = []

minimum_subject_nodes = 20
maximum_subject_nodes = 30
maximum_resource_nodes = 30
minimum_resource_node = 25
maximum_rules = 25
maximum_contexts = 15
biggestCon = 0

for node in range(0, random.randrange(minimum_resource_node, maximum_subject_nodes, 1)):
    Python_Sub_Graph["s"+str(node)] = []
    for childNode in range(0, node):
        if random.randint(0, 1):
            Python_Sub_Graph["s"+str(node)].append("s"+str(childNode))

for node in range(0, random.randrange(minimum_resource_node, maximum_resource_nodes, 1)):
    Python_Res_Graph["r"+str(node)] = []
    for childNode in range(0, node):
        if random.randint(0, 1):
            Python_Res_Graph["r"+str(node)].append("r"+str(childNode))

for context in range(0, random.randrange(1, maximum_contexts, 1)):
    Python_Context.append("c"+str(context))

for rule in range(0, random.randrange(1, maximum_rules, 1)):
    Python_Rules["rule"+str(rule)] = []
    Python_Rules["rule"+str(rule)].append("s"+str(random.randint(0, len(Python_Sub_Graph.keys())-1)))  # Subject
    Python_Rules["rule"+str(rule)].append("r"+str(random.randint(0, len(Python_Res_Graph.keys())-1)))  # Resource
    if random.randint(0, 1):
        Python_Rules["rule" + str(rule)].append("prohibition")  # Modality
    else:
        Python_Rules["rule" + str(rule)].append("permission")  # Modality
    Python_Rules["rule"+str(rule)].append(random.randint(0, 4))  # Priority
    contextsVector = []
    for i in range(0, random.randint(1, len(Python_Context))):
        randomInt = random.randint(0, len(Python_Context)-1)
        randomContext = "c"+str(randomInt)
        if randomContext not in contextsVector:
            contextsVector.append(randomContext)
            if randomInt > biggestCon:
                biggestCon = randomInt
    Python_Rules["rule"+str(rule)].append(contextsVector)

set_functions.transitive_closure(Python_Sub_Graph, Python_Sub_Closure_Graph)
set_functions.transitive_closure(Python_Res_Graph, Python_Res_Closure_Graph)

f = open("SGAC_random.txt", "w+")
f.write(str(Python_Sub_Graph)), f.write("\n")
f.write(str(Python_Res_Graph)), f.write("\n")
f.write(str(Python_Context)), f.write("\n")
f.write(str(Python_Rules)), f.write("\n")
f.write(str(Python_Sub_Closure_Graph)), f.write("\n")
f.write(str(Python_Res_Closure_Graph))
f.close()

tab = "    "
V_SUB = ""
V_RES = ""
RULE_T = ""
graph_res = ""
graph_sub = ""
rules = ""
CONTEXT = ""
MODALITY = "{per, pro}"

for key in Python_Sub_Graph.keys():
    V_SUB += str(key)+", "
    for node in Python_Sub_Graph[key]:
        graph_sub += str(key)+"|->"+str(node)+", "

for key in Python_Res_Graph.keys():
    V_RES += str(key)+", "
    for node in Python_Res_Graph[key]:
        graph_res += str(key)+"|->"+str(node)+", "

for i in range(0, biggestCon+1):
    CONTEXT += "c"+str(i)+", "

for key in Python_Rules.keys():
    RULE_T += key+", "
    rules += key+"|->(rec("
    rules += "su:"+Python_Rules[key][0]+","
    rules += "re:"+Python_Rules[key][1]+","
    if Python_Rules[key][2] == "permission":
        rules += "mo:per,"
    else:
        rules += "mo:pro,"
    rules += "pr: "+str(Python_Rules[key][3])+","
    rules += "co:{"
    for con in Python_Rules[key][4]:
        rules += con+","
    rules = rules[:len(rules)-1:]+"})), "

bmachine = "/*test/SGAC.mch\nAuthor: Diego Oliveira\n*/\n\n"
bmachine += "MACHINE\n"+tab+"SGAC\n\nDEFINITIONS\n"+tab+"SET_PREF_MAX_OPERATIONS == 1000;\n"
bmachine += tab+"applicable_def(req) == {rul | is_applicable(req,rul)};\n"\
            +tab+"is_applicable(req,rul) == ( rul : RULE_T & dom({req}) <: cl_e_sub[{(rules(rul))'su}] \\/ " \
                 "{(rules(rul))'su} & ran({req}) <: cl_e_res[{(rules(rul))'re}] \\/ {(rules(rul))'re});\n"
bmachine += tab+"maxElem(req) == {rul | rul : applicable(req) & not(#rul2.(rul2:applicable(req) & rul|->rul2: " \
                "lessSpecific))};\n"
bmachine += tab+"access_def(req,con) == (!rsinks.(rsinks: pseudoSink(req,con) => (rules(rsinks))'mo = per) & " \
                "pseudoSink(req,con)/={});\n"
bmachine += tab+"ruleSucc == %xx.(xx:REQUEST_T | {yy,zz| yy:applicable(xx) & zz:applicable(xx) & yy|->zz : " \
                "isPrecededBy(xx) & not(#uu.(uu : RULE_T & yy |-> uu : isPrecededBy(xx) & uu |-> zz : " \
                "isPrecededBy(xx) & uu /= yy & uu /= zz))})\n\n"
bmachine += "SETS\n"+tab+"/*context type*/\n"+tab+"CONTEXT={"+CONTEXT[:len(CONTEXT)-2:]+"};\n"
bmachine += tab+"/*subject vertex type*/\n"+tab+"V_SUB={"+V_SUB[:len(V_SUB)-2:]+"};\n"
bmachine += tab+"/*resource vertex type*/\n"+tab+"V_RES={"+V_RES[:len(V_RES)-2:]+"};\n"
bmachine += tab+"/*rule type*/\n"+tab+"RULE_T={"+RULE_T[:len(RULE_T)-2:]+"};\n"
bmachine += tab+"/* modality type*/\n"+tab+"MODALITY="+MODALITY+"\n\n"
bmachine += "CONSTANTS\n"+tab+"/*set of all requests*/\n"+tab+"REQUEST_T,\n"
bmachine += tab+"/*set of rules of the policy*/\n"+tab+"rules,\n"
bmachine += tab+"/*edges of the subject graph*/\n"+tab+"e_sub,\n"
bmachine += tab+"/*resource graph edges*/\n"+tab+"e_res,\n"
bmachine += tab+"/*ordering 1: lessSpecific*/\n"+tab+"lessSpecific,\n"
bmachine += tab+"/*closure1 of e_sub, closure of e_sub, e_res*/\n"+tab+"cl1_e_sub,cl_e_sub,cl1_e_res,cl_e_res\n\n"
bmachine += "PROPERTIES\n"+tab+"/*types*/\n"+tab+"e_sub: V_SUB <-> V_SUB &\n"
bmachine += tab+"e_res : V_RES <-> V_RES &\n"
bmachine += tab+"REQUEST_T = (V_SUB-dom(e_sub)) * (V_RES-dom(e_res)) &\n"
bmachine += tab+"/*rules: function that maps a rule to the rule structure*/\n"
bmachine += tab+"rules: RULE_T --> (struct(su:V_SUB, re:V_RES, mo: MODALITY, pr:INTEGER, co:POW(CONTEXT))) &\n"
bmachine += tab+"lessSpecific : RULE_T <-> RULE_T & \n\n"
bmachine += tab+"/* closure definitions */\n"
bmachine += tab+"cl1_e_sub = closure1(e_sub) &\n"
bmachine += tab+"cl_e_sub = closure(e_sub) &\n"
bmachine += tab+"cl1_e_res = closure1(e_res) &\n"
bmachine += tab+"cl_e_res = closure(e_res) &\n"
bmachine += tab+"/*acyclicity of the graphs */\n"
bmachine += tab+"cl1_e_sub /\\ id(V_SUB) = {} &\n"
bmachine += tab+"cl1_e_res /\\ id(V_RES) = {} &\n\n"
bmachine += tab+"/* Constraints for rule ordering */\n"
bmachine += tab+"/* lessSpecific definition */\n"
bmachine += tab+"lessSpecific = {xx,yy | xx: dom(rules) & yy: dom(rules) & ((((rules(xx))'pr > (rules(yy))'pr) or " \
                "(((rules(xx))'pr = (rules(yy))'pr) & (rules(yy))'su: cl1_e_sub[{(rules(xx))'su}])))}&\n\n"
bmachine += tab+"/* pseudo INITIALISATION  */\n"
bmachine += tab+"/* THE GRAPHS */\n"
bmachine += tab+"e_sub={"+graph_sub[:len(graph_sub)-2:]+"} &\n"
bmachine += tab+"e_res={"+graph_res[:len(graph_res)-2:]+"} &\n"
bmachine += tab+"rules={"+rules[:len(rules)-2:]+"}\n\n"
bmachine += "VARIABLES\n"
bmachine += tab+"/*applicable: contains all applicable rule to a request*/\n"+tab+"applicable,\n"
bmachine += tab+"/*conRule: associate a condition to its rules*/\n"+tab+"conRule,\n"
bmachine += tab+"/*ordering 2:isPrecededBy*/\n"+tab+"isPrecededBy,\n"
bmachine += tab+"/*closure of ruleSucc*/\n"+tab+"cl1_ruleSucc,\n"
bmachine += tab+"/*function returning the pseudosinks of a request+context*/\n"+tab+"pseudoSink\n\n"
bmachine += "INVARIANT\n"+tab+"applicable :  REQUEST_T -->POW(RULE_T) &\n"
bmachine += tab+"conRule : CONTEXT --> POW(RULE_T) &\n"+tab+"isPrecededBy : REQUEST_T --> (RULE_T <-> RULE_T) &\n"
bmachine += tab+"cl1_ruleSucc : REQUEST_T --> (RULE_T <-> RULE_T) &\n"+tab+"pseudoSink : (REQUEST_T * CONTEXT)-->" \
                                                                           " POW(RULE_T)\n\n"
bmachine += "INITIALISATION\n"+tab+"BEGIN\n"+tab+"applicable :=  %rr.(rr:REQUEST_T|applicable_def(rr));\n"
bmachine += tab+"conRule := %con.(con:CONTEXT|{cc|cc:dom(rules) & con : (rules(cc))'co});\n"
bmachine += tab+"/*isPrecededBy definition*/\n"
bmachine += tab+"isPrecededBy := %xx.(xx:REQUEST_T | {yy, zz | yy:applicable(xx) & zz:applicable(xx) & yy/=zz & (" \
                "yy|->zz : lessSpecific or ({yy,zz}<:maxElem(xx) & (rules(yy))'mo = per & (rules(zz))'mo = pro))});\n"
bmachine += tab+"cl1_ruleSucc := %xx.(xx:REQUEST_T | closure1(isPrecededBy(xx)));\n"
bmachine += tab+"pseudoSink := %(req,con).(req:REQUEST_T & con:dom(conRule) | {ru | ru : applicable(req) &" \
                "ru : conRule(con) & !subrule.(subrule : cl1_ruleSucc(req)[{ru}] => not( subrule: conRule(con)))})\n"
bmachine += tab+"END\n\n"
bmachine += "OPERATIONS\n"+tab+"/*checks the access from the request req under the context con*/\n"
bmachine += tab+"access <-- CheckAccess(req, con)=\n"+tab+"PRE\n"+tab+tab+"req : REQUEST_T & con : CONTEXT\n"+tab + \
            "THEN\n"+tab+tab+"access := bool(access_def(req,con))\n"+tab+"END;\n\n"
bmachine += tab+"/*checks if there is a hidden document under the context con*/\n"
bmachine += tab+"hidden<-- HiddenDocument(con)=\n"+tab+"PRE\n"
bmachine += tab+tab+"con : CONTEXT\n"+tab+"THEN\n"
bmachine += tab+tab+"hidden := bool(#(hdoc).(hdoc:(V_RES - dom(e_res)) & !req.((req:REQUEST_T & " \
                    "prj2(V_SUB,V_RES)(req)=hdoc) => not(access_def(req,con)))))\n"+tab+"END;\n\n"
bmachine += tab+"/*returns the set of the hidden documents under the condition con*/\n"
bmachine += tab+"hiddenSet <-- HiddenDataSet(con)=\n"+tab+"PRE\n"
bmachine += tab+tab+"con : CONTEXT\n"+tab+"THEN\n"
bmachine += tab+tab+"hiddenSet := { hdoc | hdoc : V_RES - dom(e_res) & !req.((req:REQUEST_T & " \
                    "prj2(V_SUB,V_RES)(req)=hdoc) => not(access_def(req,con)))}\n"+tab+"END;\n\n"
bmachine += tab+"/*determines the contexts that grant a request*/\n"
bmachine += tab+"granting <-- GrantingContexts(req)=\n"+tab+"PRE\n"
bmachine += tab+tab+"req : REQUEST_T\n"+tab+"THEN\n"
bmachine += tab+tab+"granting := { con | con : CONTEXT & access_def(req,con)}\n"+tab+"END;\n\n"
bmachine += tab+"/*returns the set of the rules that are never used*/\n"
bmachine += tab+"ineffectiveSet <-- IneffectiveRuleSet =\n"+tab+"BEGIN\n"
bmachine += tab+tab+"ineffectiveSet := {ru | ru : RULE_T & not(#(req,con).(req:REQUEST_T & ru : conRule(con) &" \
                    "ru : pseudoSink(req,con) &	(pseudoSink(req,con) - {ru} = {} or((rules(ru))'mo = pro & " \
                    "!ru2.(ru2:(pseudoSink(req,con)-{ru}) => (rules(ru2))'mo = per)))))}\n"+tab+"END\n"
bmachine += "END"

f = open("SGAC_random_B.mch", "w+")
f.write(bmachine)
f.close()
