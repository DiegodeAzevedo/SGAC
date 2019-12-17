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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24};
    /*rule type*/
    RULE_T={rule0, rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8, rule9, rule10, rule11, rule12};
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
    e_sub={s1|->s0, s2|->s1, s3|->s0, s3|->s1, s3|->s2, s5|->s1, s5|->s2, s5|->s4, s6|->s0, s6|->s1, s6|->s3, s7|->s3, s7|->s5, s8|->s0, s8|->s3, s8|->s4, s9|->s0, s9|->s1, s9|->s4, s9|->s5, s10|->s0, s10|->s2, s10|->s3, s10|->s7, s10|->s8, s11|->s1, s11|->s2, s11|->s5, s11|->s6, s11|->s7, s11|->s9, s12|->s4, s12|->s6, s12|->s7, s12|->s8, s12|->s9, s12|->s10, s12|->s11, s13|->s1, s13|->s4, s13|->s5, s13|->s6, s13|->s7, s13|->s9, s13|->s11, s13|->s12, s14|->s0, s14|->s1, s14|->s4, s14|->s5, s14|->s6, s14|->s7, s14|->s10, s14|->s12, s15|->s0, s15|->s2, s15|->s4, s15|->s5, s15|->s6, s15|->s8, s15|->s12, s15|->s13, s15|->s14, s16|->s1, s16|->s2, s16|->s3, s16|->s5, s16|->s9, s16|->s13, s16|->s15, s17|->s1, s17|->s2, s17|->s4, s17|->s5, s17|->s6, s17|->s7, s17|->s9, s17|->s10, s17|->s11, s17|->s12, s17|->s13, s17|->s14, s18|->s0, s18|->s8, s18|->s10, s18|->s12, s18|->s13, s18|->s14, s18|->s16, s18|->s17, s19|->s4, s19|->s6, s19|->s7, s19|->s10, s19|->s13, s19|->s17, s20|->s0, s20|->s1, s20|->s4, s20|->s7, s20|->s8, s20|->s9, s20|->s10, s20|->s11, s20|->s12, s20|->s15, s20|->s16, s20|->s18, s21|->s0, s21|->s1, s21|->s2, s21|->s3, s21|->s5, s21|->s6, s21|->s7, s21|->s8, s21|->s10, s21|->s13, s21|->s15, s21|->s16, s21|->s20, s22|->s2, s22|->s4, s22|->s10, s22|->s12, s22|->s13, s22|->s19, s23|->s0, s23|->s1, s23|->s2, s23|->s6, s23|->s7, s23|->s12, s23|->s13, s23|->s16, s23|->s17, s23|->s18, s23|->s19, s23|->s20, s24|->s0, s24|->s1, s24|->s2, s24|->s3, s24|->s6, s24|->s7, s24|->s8, s24|->s9, s24|->s12, s24|->s17, s24|->s20, s24|->s23} &
    e_res={r3|->r0, r3|->r1, r4|->r0, r4|->r1, r4|->r2, r5|->r0, r5|->r3, r5|->r4, r6|->r4, r6|->r5, r7|->r0, r7|->r1, r7|->r3, r7|->r5, r8|->r0, r8|->r1, r8|->r2, r8|->r3, r8|->r4, r8|->r5, r8|->r7, r9|->r1, r9|->r3, r9|->r6, r9|->r8, r10|->r0, r10|->r1, r10|->r2, r10|->r3, r10|->r7, r10|->r8, r10|->r9, r11|->r3, r11|->r5, r11|->r6, r11|->r7, r11|->r10, r12|->r4, r12|->r5, r12|->r6, r12|->r7, r12|->r8, r12|->r11, r13|->r1, r13|->r2, r13|->r5, r13|->r6, r13|->r7, r13|->r9, r13|->r11, r13|->r12, r14|->r0, r14|->r1, r14|->r3, r14|->r8, r14|->r9, r14|->r11, r14|->r12, r14|->r13, r15|->r2, r15|->r3, r15|->r5, r15|->r6, r15|->r9, r15|->r11, r15|->r13, r16|->r10, r16|->r11, r16|->r15, r17|->r3, r17|->r7, r17|->r11, r17|->r13, r18|->r0, r18|->r2, r18|->r3, r18|->r4, r18|->r8, r18|->r9, r18|->r10, r18|->r11, r18|->r16, r18|->r17, r19|->r0, r19|->r4, r19|->r5, r19|->r7, r19|->r8, r19|->r10, r19|->r11, r19|->r12, r19|->r13, r19|->r14, r19|->r16, r19|->r17, r19|->r18, r20|->r0, r20|->r1, r20|->r2, r20|->r3, r20|->r4, r20|->r6, r20|->r7, r20|->r9, r20|->r10, r20|->r13, r20|->r16, r20|->r17, r21|->r0, r21|->r5, r21|->r6, r21|->r7, r21|->r8, r21|->r9, r21|->r10, r21|->r11, r21|->r16, r21|->r19, r21|->r20, r22|->r0, r22|->r1, r22|->r4, r22|->r5, r22|->r9, r22|->r11, r22|->r12, r22|->r13, r22|->r16, r22|->r17, r22|->r18, r22|->r20, r23|->r0, r23|->r4, r23|->r6, r23|->r8, r23|->r11, r23|->r12, r23|->r18, r24|->r0, r24|->r2, r24|->r3, r24|->r5, r24|->r6, r24|->r9, r24|->r12, r24|->r14, r24|->r16, r24|->r17, r24|->r18, r24|->r19, r24|->r20} &
    rules={rule0|->(rec(su:s20,re:r16,mo:per,pr: 3,co:{c8,c3,c1,c4,c2,c7})), rule1|->(rec(su:s23,re:r22,mo:per,pr: 1,co:{c3,c7})), rule2|->(rec(su:s11,re:r9,mo:pro,pr: 0,co:{c9,c4,c3})), rule3|->(rec(su:s15,re:r14,mo:pro,pr: 0,co:{c8,c0,c5,c9})), rule4|->(rec(su:s1,re:r2,mo:per,pr: 1,co:{c0,c6,c7,c4,c1,c5})), rule5|->(rec(su:s1,re:r10,mo:per,pr: 4,co:{c1,c4,c6})), rule6|->(rec(su:s13,re:r22,mo:pro,pr: 4,co:{c8,c6,c3,c7,c2,c4})), rule7|->(rec(su:s20,re:r24,mo:per,pr: 4,co:{c4,c6})), rule8|->(rec(su:s11,re:r23,mo:pro,pr: 1,co:{c0,c7,c6,c9,c4,c8})), rule9|->(rec(su:s3,re:r24,mo:pro,pr: 3,co:{c6,c7,c1,c8,c4})), rule10|->(rec(su:s19,re:r4,mo:per,pr: 3,co:{c6,c4,c3,c1})), rule11|->(rec(su:s15,re:r23,mo:pro,pr: 1,co:{c7,c1,c0,c5,c3,c2})), rule12|->(rec(su:s9,re:r17,mo:per,pr: 4,co:{c6,c9,c0,c7}))}

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