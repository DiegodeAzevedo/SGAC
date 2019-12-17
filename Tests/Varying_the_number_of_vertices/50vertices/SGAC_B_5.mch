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
    e_sub={s2|->s0, s3|->s0, s3|->s1, s4|->s0, s4|->s1, s5|->s0, s5|->s2, s6|->s2, s7|->s1, s7|->s2, s7|->s3, s7|->s5, s7|->s6, s8|->s1, s8|->s2, s8|->s7, s9|->s0, s9|->s3, s9|->s4, s9|->s5, s9|->s8, s10|->s0, s10|->s1, s10|->s2, s10|->s3, s10|->s5, s10|->s7, s11|->s1, s11|->s2, s11|->s3, s11|->s7, s11|->s8, s11|->s9, s12|->s3, s12|->s4, s12|->s5, s12|->s7, s12|->s8, s12|->s9, s12|->s10, s12|->s11, s13|->s0, s13|->s1, s13|->s2, s13|->s3, s13|->s8, s13|->s11, s14|->s0, s14|->s1, s14|->s3, s14|->s4, s14|->s5, s14|->s8, s14|->s10, s14|->s11, s14|->s12, s15|->s0, s15|->s2, s15|->s4, s15|->s7, s15|->s10, s15|->s14, s16|->s1, s16|->s3, s16|->s4, s16|->s6, s16|->s7, s16|->s8, s16|->s10, s16|->s11, s16|->s13, s17|->s0, s17|->s1, s17|->s2, s17|->s4, s17|->s10, s17|->s11, s17|->s13, s17|->s15, s17|->s16, s18|->s2, s18|->s3, s18|->s8, s18|->s10, s18|->s11, s18|->s14, s18|->s17, s19|->s6, s19|->s8, s19|->s9, s19|->s13, s19|->s14, s19|->s16, s20|->s4, s20|->s13, s20|->s14, s20|->s17, s20|->s18, s21|->s1, s21|->s2, s21|->s3, s21|->s4, s21|->s5, s21|->s7, s21|->s9, s21|->s10, s21|->s11, s21|->s12, s21|->s17, s21|->s18, s21|->s19, s22|->s0, s22|->s2, s22|->s3, s22|->s4, s22|->s6, s22|->s7, s22|->s9, s22|->s12, s22|->s14, s22|->s20, s22|->s21, s23|->s1, s23|->s2, s23|->s3, s23|->s4, s23|->s5, s23|->s8, s23|->s9, s23|->s10, s23|->s11, s23|->s13, s23|->s14, s23|->s15, s23|->s17, s23|->s20, s23|->s22, s24|->s0, s24|->s2, s24|->s6, s24|->s7, s24|->s8, s24|->s9, s24|->s10, s24|->s13, s24|->s14, s24|->s15, s24|->s16, s24|->s21, s24|->s22, s24|->s23} &
    e_res={r3|->r2, r4|->r0, r4|->r1, r5|->r0, r5|->r1, r5|->r3, r6|->r1, r6|->r3, r6|->r4, r6|->r5, r7|->r1, r7|->r3, r7|->r4, r7|->r5, r7|->r6, r8|->r0, r8|->r1, r8|->r2, r8|->r4, r8|->r5, r8|->r6, r8|->r7, r9|->r3, r9|->r7, r9|->r8, r10|->r1, r10|->r3, r10|->r5, r10|->r6, r10|->r7, r10|->r8, r10|->r9, r11|->r0, r11|->r1, r11|->r6, r11|->r7, r11|->r9, r11|->r10, r12|->r2, r12|->r3, r12|->r4, r12|->r5, r12|->r8, r12|->r9, r12|->r10, r13|->r0, r13|->r2, r13|->r4, r13|->r7, r13|->r9, r14|->r1, r14|->r3, r14|->r4, r14|->r5, r14|->r6, r14|->r9, r14|->r10, r14|->r11, r14|->r12, r14|->r13, r15|->r0, r15|->r3, r15|->r7, r15|->r8, r15|->r14, r16|->r3, r16|->r5, r16|->r9, r16|->r10, r16|->r12, r16|->r13, r16|->r14, r17|->r1, r17|->r4, r17|->r5, r17|->r7, r17|->r8, r17|->r9, r17|->r10, r17|->r12, r17|->r13, r17|->r14, r17|->r16, r18|->r1, r18|->r3, r18|->r6, r18|->r7, r18|->r8, r18|->r12, r18|->r14, r18|->r15, r19|->r1, r19|->r4, r19|->r6, r19|->r7, r19|->r8, r19|->r12, r19|->r14, r20|->r1, r20|->r2, r20|->r6, r20|->r8, r20|->r10, r20|->r17, r21|->r4, r21|->r6, r21|->r7, r21|->r8, r21|->r10, r21|->r13, r21|->r20, r22|->r2, r22|->r6, r22|->r7, r22|->r8, r22|->r9, r22|->r10, r22|->r11, r22|->r12, r22|->r14, r22|->r16, r22|->r17, r22|->r18, r22|->r21, r23|->r2, r23|->r3, r23|->r4, r23|->r6, r23|->r9, r23|->r11, r23|->r12, r23|->r17, r23|->r18, r23|->r19, r23|->r22, r24|->r0, r24|->r1, r24|->r2, r24|->r3, r24|->r6, r24|->r7, r24|->r10, r24|->r11, r24|->r13, r24|->r17, r24|->r19, r24|->r20} &
    rules={rule0|->(rec(su:s5,re:r7,mo:pro,pr: 3,co:{c9,c4,c0})), rule1|->(rec(su:s19,re:r4,mo:pro,pr: 3,co:{c1,c8,c0,c9,c4,c2})), rule2|->(rec(su:s6,re:r20,mo:per,pr: 4,co:{c8,c4,c5,c6,c7,c0,c3,c1})), rule3|->(rec(su:s12,re:r23,mo:per,pr: 2,co:{c2,c9,c7,c3,c4})), rule4|->(rec(su:s24,re:r21,mo:pro,pr: 2,co:{c9,c1,c7,c5})), rule5|->(rec(su:s14,re:r24,mo:per,pr: 4,co:{c7,c0,c5})), rule6|->(rec(su:s14,re:r13,mo:per,pr: 2,co:{c0,c3,c2,c5,c8,c4})), rule7|->(rec(su:s21,re:r0,mo:pro,pr: 2,co:{c6,c4,c0})), rule8|->(rec(su:s12,re:r24,mo:pro,pr: 0,co:{c6})), rule9|->(rec(su:s22,re:r19,mo:per,pr: 4,co:{c0,c4,c5,c8,c6,c3})), rule10|->(rec(su:s20,re:r6,mo:per,pr: 2,co:{c8,c0,c5})), rule11|->(rec(su:s0,re:r14,mo:per,pr: 1,co:{c9,c8,c6,c7})), rule12|->(rec(su:s3,re:r24,mo:pro,pr: 1,co:{c3,c4,c9,c0,c7}))}

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