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
    RULE_T={rule0, rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8, rule9, rule10, rule11, rule12, rule13, rule14, rule15, rule16, rule17, rule18};
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
    e_sub={s2|->s0, s2|->s1, s3|->s1, s4|->s0, s4|->s1, s4|->s2, s4|->s3, s5|->s0, s5|->s1, s5|->s3, s5|->s4, s6|->s0, s6|->s1, s7|->s0, s7|->s1, s7|->s2, s7|->s3, s7|->s5, s8|->s1, s8|->s3, s8|->s5, s8|->s6, s8|->s7, s9|->s1, s9|->s2, s9|->s3, s9|->s4, s9|->s5, s9|->s6, s10|->s0, s10|->s3, s10|->s4, s10|->s6, s10|->s7, s10|->s8, s10|->s9, s11|->s7, s11|->s8, s12|->s2, s12|->s5, s12|->s9, s12|->s10, s12|->s11, s13|->s3, s13|->s4, s13|->s5, s13|->s6, s13|->s9, s13|->s10, s13|->s11, s14|->s2, s14|->s3, s14|->s4, s14|->s9, s14|->s11, s15|->s0, s15|->s1, s15|->s3, s15|->s4, s15|->s5, s15|->s6, s15|->s8, s15|->s9, s15|->s10, s15|->s11, s15|->s14, s16|->s0, s16|->s1, s16|->s6, s16|->s7, s16|->s9, s16|->s12, s16|->s13, s16|->s15, s17|->s0, s17|->s2, s17|->s4, s17|->s5, s17|->s10, s17|->s12, s17|->s15, s18|->s1, s18|->s2, s18|->s5, s18|->s6, s18|->s7, s18|->s8, s18|->s13, s18|->s14, s18|->s15, s18|->s16, s19|->s0, s19|->s2, s19|->s5, s19|->s6, s19|->s11, s19|->s13, s19|->s15, s19|->s16, s19|->s18} &
    e_res={r2|->r0, r2|->r1, r4|->r2, r5|->r4, r6|->r0, r6|->r1, r6|->r2, r6|->r4, r7|->r1, r8|->r0, r8|->r3, r8|->r5, r8|->r6, r8|->r7, r9|->r0, r9|->r1, r9|->r2, r9|->r5, r9|->r6, r9|->r8, r10|->r1, r10|->r3, r10|->r5, r10|->r8, r11|->r5, r11|->r6, r11|->r7, r12|->r0, r12|->r3, r12|->r7, r12|->r9, r12|->r10, r12|->r11, r13|->r0, r13|->r2, r13|->r5, r13|->r7, r13|->r8, r13|->r9, r13|->r11, r13|->r12, r14|->r3, r14|->r6, r14|->r8, r14|->r10, r14|->r12, r15|->r0, r15|->r2, r15|->r3, r15|->r4, r15|->r9, r15|->r10, r15|->r12, r15|->r13, r15|->r14, r16|->r0, r16|->r2, r16|->r4, r16|->r5, r16|->r7, r16|->r10, r16|->r13, r16|->r15, r17|->r0, r17|->r1, r17|->r2, r17|->r3, r17|->r5, r17|->r6, r17|->r8, r17|->r9, r17|->r11, r17|->r15, r17|->r16, r18|->r1, r18|->r2, r18|->r3, r18|->r5, r18|->r6, r18|->r10, r18|->r12, r18|->r13, r18|->r14, r18|->r15, r18|->r16, r18|->r17, r19|->r0, r19|->r1, r19|->r2, r19|->r4, r19|->r6, r19|->r8, r19|->r10, r19|->r11, r19|->r13, r19|->r15, r19|->r16, r19|->r18} &
    rules={rule0|->(rec(su:s3,re:r17,mo:pro,pr: 3,co:{c9,c4,c8,c3,c0,c1,c6})), rule1|->(rec(su:s9,re:r16,mo:per,pr: 0,co:{c0,c1,c2,c3,c4})), rule2|->(rec(su:s13,re:r14,mo:pro,pr: 1,co:{c7,c1,c4,c0,c8,c9})), rule3|->(rec(su:s17,re:r0,mo:pro,pr: 0,co:{c5,c8})), rule4|->(rec(su:s1,re:r6,mo:per,pr: 1,co:{c9,c7,c4})), rule5|->(rec(su:s15,re:r11,mo:pro,pr: 2,co:{c5,c4,c2,c1,c6})), rule6|->(rec(su:s16,re:r19,mo:per,pr: 4,co:{c4})), rule7|->(rec(su:s1,re:r3,mo:pro,pr: 3,co:{c8,c1,c9,c3,c0,c7})), rule8|->(rec(su:s7,re:r7,mo:pro,pr: 0,co:{c9,c4,c6,c5})), rule9|->(rec(su:s3,re:r5,mo:pro,pr: 0,co:{c5,c7,c4,c1,c9,c6})), rule10|->(rec(su:s5,re:r18,mo:pro,pr: 0,co:{c9})), rule11|->(rec(su:s13,re:r11,mo:per,pr: 1,co:{c4,c0,c1,c6})), rule12|->(rec(su:s7,re:r13,mo:pro,pr: 0,co:{c5,c1,c9,c4,c7,c2,c8})), rule13|->(rec(su:s16,re:r8,mo:per,pr: 3,co:{c7,c0})), rule14|->(rec(su:s6,re:r7,mo:per,pr: 0,co:{c5,c3,c1,c4,c0,c9,c7})), rule15|->(rec(su:s6,re:r17,mo:per,pr: 4,co:{c7,c2,c4,c9,c8,c3,c0})), rule16|->(rec(su:s19,re:r19,mo:per,pr: 0,co:{c0,c4,c5,c6,c8,c1,c2})), rule17|->(rec(su:s13,re:r7,mo:pro,pr: 2,co:{c5,c7,c1,c6,c8,c2})), rule18|->(rec(su:s14,re:r7,mo:pro,pr: 4,co:{c9,c2}))}

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