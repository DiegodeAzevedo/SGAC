/*test/SGAC.mch
Author: Diego Oliveira
*/

MACHINE
    SGAC

DEFINITIONS
    SET_PREF_MAX_OPERATIONS == 1000;
    applicable_def(req) == {rul | is_applicable(req,rul)};
    is_applicable(req,rul) == ( rul : RULE_T & dom({req}) <: cl_e_sub[{(rules(rul))'su}] \/ {(rules(rul))'su} & ran({req}) <: cl_e_res[{(rules(rul))'re}] \/ {(rules(rul))'re});
    maxElem(req) == {rul | rul : applicable(req) & not(#rul2.(rul2:applicable(req) & rul|->rul2: lessSpecific))};
    access_def(req,con) == (!rsinks.(rsinks: pseudoSink(req,con) => (rules(rsinks))'mo = per) & pseudoSink(req,con)/={});
    ruleSucc == %xx.(xx:REQUEST_T | {yy,zz| yy:applicable(xx) & zz:applicable(xx) & yy|->zz : isPrecededBy(xx) & not(#uu.(uu : RULE_T & yy |-> uu : isPrecededBy(xx) & uu |-> zz : isPrecededBy(xx) & uu /= yy & uu /= zz))})

SETS
    /*context type*/
    CONTEXT={c0, c1, c2, c3, c4, c5, c6, c7, c8, c9};
    /*subject vertex type*/
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19};
    /*rule type*/
    RULE_T={rule0, rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8};
    /* modality type*/
    MODALITY={per, pro}

CONSTANTS
    /*set of all requests*/
    REQUEST_T,
    /*set of rules of the policy*/
    rules,
    /*edges of the subject graph*/
    e_sub,
    /*resource graph edges*/
    e_res,
    /*ordering 1: lessSpecific*/
    lessSpecific,
    /*closure1 of e_sub, closure of e_sub, e_res*/
    cl1_e_sub,cl_e_sub,cl1_e_res,cl_e_res

PROPERTIES
    /*types*/
    e_sub: V_SUB <-> V_SUB &
    e_res : V_RES <-> V_RES &
    REQUEST_T = (V_SUB-dom(e_sub)) * (V_RES-dom(e_res)) &
    /*rules: function that maps a rule to the rule structure*/
    rules: RULE_T --> (struct(su:V_SUB, re:V_RES, mo: MODALITY, pr:INTEGER, co:POW(CONTEXT))) &
    lessSpecific : RULE_T <-> RULE_T & 

    /* closure definitions */
    cl1_e_sub = closure1(e_sub) &
    cl_e_sub = closure(e_sub) &
    cl1_e_res = closure1(e_res) &
    cl_e_res = closure(e_res) &
    /*acyclicity of the graphs */
    cl1_e_sub /\ id(V_SUB) = {} &
    cl1_e_res /\ id(V_RES) = {} &

    /* Constraints for rule ordering */
    /* lessSpecific definition */
    lessSpecific = {xx,yy | xx: dom(rules) & yy: dom(rules) & ((((rules(xx))'pr > (rules(yy))'pr) or (((rules(xx))'pr = (rules(yy))'pr) & (rules(yy))'su: cl1_e_sub[{(rules(xx))'su}])))}&

    /* pseudo INITIALISATION  */
    /* THE GRAPHS */
    e_sub={s2|->s0, s3|->s1, s4|->s1, s4|->s2, s4|->s3, s5|->s0, s5|->s1, s5|->s2, s5|->s4, s6|->s1, s6|->s2, s6|->s4, s7|->s0, s7|->s4, s7|->s5, s8|->s1, s8|->s2, s8|->s3, s8|->s6, s9|->s0, s9|->s1, s9|->s5, s10|->s0, s10|->s1, s10|->s4, s10|->s5, s10|->s7, s10|->s8, s11|->s2, s11|->s4, s11|->s5, s11|->s6, s12|->s1, s12|->s2, s12|->s3, s12|->s5, s12|->s6, s12|->s9, s12|->s10, s12|->s11, s13|->s0, s13|->s1, s13|->s4, s13|->s5, s13|->s6, s13|->s12, s14|->s0, s14|->s1, s14|->s3, s14|->s4, s14|->s5, s14|->s8, s14|->s9, s14|->s12, s15|->s0, s15|->s1, s15|->s3, s15|->s5, s15|->s6, s15|->s10, s15|->s12, s16|->s2, s16|->s3, s16|->s5, s16|->s6, s16|->s7, s16|->s10, s16|->s14, s17|->s0, s17|->s1, s17|->s3, s17|->s9, s17|->s10, s17|->s11, s17|->s13, s17|->s14, s18|->s0, s18|->s2, s18|->s3, s18|->s5, s18|->s6, s18|->s8, s18|->s11, s18|->s13, s18|->s15, s18|->s17, s19|->s2, s19|->s5, s19|->s8, s19|->s9, s19|->s14, s19|->s16, s19|->s17, s19|->s18} &
    e_res={r1|->r0, r2|->r0, r3|->r1, r4|->r2, r4|->r3, r5|->r1, r5|->r2, r5|->r3, r5|->r4, r6|->r4, r7|->r4, r7|->r5, r7|->r6, r8|->r1, r8|->r3, r8|->r4, r8|->r6, r9|->r0, r9|->r2, r9|->r3, r9|->r4, r10|->r0, r10|->r2, r10|->r4, r10|->r8, r11|->r2, r11|->r7, r11|->r8, r11|->r9, r11|->r10, r12|->r0, r12|->r6, r12|->r10, r12|->r11, r13|->r2, r13|->r4, r13|->r6, r13|->r8, r13|->r11, r13|->r12, r14|->r1, r14|->r3, r14|->r6, r14|->r8, r14|->r10, r14|->r13, r15|->r1, r15|->r2, r15|->r6, r15|->r8, r15|->r10, r16|->r1, r16|->r4, r16|->r5, r16|->r7, r16|->r10, r16|->r13, r16|->r15, r17|->r6, r17|->r7, r17|->r9, r17|->r10, r17|->r12, r17|->r13, r17|->r14, r17|->r16, r18|->r0, r18|->r6, r18|->r8, r18|->r13, r19|->r2, r19|->r5, r19|->r6, r19|->r8, r19|->r9, r19|->r16, r19|->r17, r19|->r18} &
    rules={rule0|->(rec(su:s13,re:r8,mo:pro,pr: 1,co:{c2,c9,c0,c5,c7,c3})), rule1|->(rec(su:s12,re:r0,mo:per,pr: 3,co:{c5,c8,c2,c1,c6})), rule2|->(rec(su:s19,re:r4,mo:pro,pr: 1,co:{c3,c9})), rule3|->(rec(su:s3,re:r8,mo:pro,pr: 1,co:{c1,c2,c5,c4,c7,c6})), rule4|->(rec(su:s0,re:r7,mo:pro,pr: 1,co:{c4,c0,c6,c8,c9,c1})), rule5|->(rec(su:s2,re:r6,mo:per,pr: 3,co:{c9,c6})), rule6|->(rec(su:s12,re:r18,mo:per,pr: 2,co:{c5,c4,c7,c6,c0,c1})), rule7|->(rec(su:s12,re:r9,mo:per,pr: 2,co:{c0,c6,c2,c8,c3,c4})), rule8|->(rec(su:s12,re:r16,mo:pro,pr: 0,co:{c9,c4,c8,c1,c5}))}

VARIABLES
    /*applicable: contains all applicable rule to a request*/
    applicable,
    /*conRule: associate a condition to its rules*/
    conRule,
    /*ordering 2:isPrecededBy*/
    isPrecededBy,
    /*closure of ruleSucc*/
    cl1_ruleSucc,
    /*function returning the pseudosinks of a request+context*/
    pseudoSink

INVARIANT
    applicable :  REQUEST_T -->POW(RULE_T) &
    conRule : CONTEXT --> POW(RULE_T) &
    isPrecededBy : REQUEST_T --> (RULE_T <-> RULE_T) &
    cl1_ruleSucc : REQUEST_T --> (RULE_T <-> RULE_T) &
    pseudoSink : (REQUEST_T * CONTEXT)--> POW(RULE_T)

INITIALISATION
    BEGIN
    applicable :=  %rr.(rr:REQUEST_T|applicable_def(rr));
    conRule := %con.(con:CONTEXT|{cc|cc:dom(rules) & con : (rules(cc))'co});
    /*isPrecededBy definition*/
    isPrecededBy := %xx.(xx:REQUEST_T | {yy, zz | yy:applicable(xx) & zz:applicable(xx) & yy/=zz & (yy|->zz : lessSpecific or ({yy,zz}<:maxElem(xx) & (rules(yy))'mo = per & (rules(zz))'mo = pro))});
    cl1_ruleSucc := %xx.(xx:REQUEST_T | closure1(isPrecededBy(xx)));
    pseudoSink := %(req,con).(req:REQUEST_T & con:dom(conRule) | {ru | ru : applicable(req) &ru : conRule(con) & !subrule.(subrule : cl1_ruleSucc(req)[{ru}] => not( subrule: conRule(con)))})
    END

OPERATIONS
    /*checks the access from the request req under the context con*/
    access <-- CheckAccess(req, con)=
    PRE
        req : REQUEST_T & con : CONTEXT
    THEN
        access := bool(access_def(req,con))
    END;

    /*checks if there is a hidden document under the context con*/
    hidden<-- HiddenDocument(con)=
    PRE
        con : CONTEXT
    THEN
        hidden := bool(#(hdoc).(hdoc:(V_RES - dom(e_res)) & !req.((req:REQUEST_T & prj2(V_SUB,V_RES)(req)=hdoc) => not(access_def(req,con)))))
    END;

    /*returns the set of the hidden documents under the condition con*/
    hiddenSet <-- HiddenDataSet(con)=
    PRE
        con : CONTEXT
    THEN
        hiddenSet := { hdoc | hdoc : V_RES - dom(e_res) & !req.((req:REQUEST_T & prj2(V_SUB,V_RES)(req)=hdoc) => not(access_def(req,con)))}
    END;

    /*determines the contexts that grant a request*/
    granting <-- GrantingContexts(req)=
    PRE
        req : REQUEST_T
    THEN
        granting := { con | con : CONTEXT & access_def(req,con)}
    END;

    /*returns the set of the rules that are never used*/
    ineffectiveSet <-- IneffectiveRuleSet =
    BEGIN
        ineffectiveSet := {ru | ru : RULE_T & not(#(req,con).(req:REQUEST_T & ru : conRule(con) &ru : pseudoSink(req,con) &	(pseudoSink(req,con) - {ru} = {} or((rules(ru))'mo = pro & !ru2.(ru2:(pseudoSink(req,con)-{ru}) => (rules(ru2))'mo = per)))))}
    END
END