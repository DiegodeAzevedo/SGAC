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
    e_sub={s3|->s0, s3|->s1, s4|->s0, s4|->s1, s5|->s1, s5|->s2, s5|->s3, s6|->s1, s6|->s3, s6|->s5, s7|->s1, s7|->s4, s7|->s5, s8|->s2, s8|->s3, s8|->s5, s8|->s6, s9|->s1, s9|->s6, s10|->s5, s10|->s7, s10|->s9, s11|->s0, s11|->s2, s11|->s4, s11|->s8, s11|->s9, s12|->s2, s12|->s3, s12|->s6, s12|->s7, s12|->s8, s12|->s10, s12|->s11, s13|->s1, s13|->s3, s13|->s5, s13|->s9, s13|->s11, s14|->s2, s14|->s3, s14|->s4, s14|->s5, s14|->s6, s14|->s10, s14|->s11, s15|->s0, s15|->s1, s15|->s3, s15|->s5, s15|->s6, s15|->s8, s15|->s9, s15|->s10, s15|->s13, s15|->s14, s16|->s2, s16|->s3, s16|->s6, s16|->s11, s16|->s15, s17|->s8, s17|->s9, s17|->s11, s17|->s13, s17|->s14, s17|->s16, s18|->s0, s18|->s4, s18|->s5, s18|->s8, s18|->s9, s18|->s13, s18|->s14, s18|->s16, s19|->s0, s19|->s3, s19|->s4, s19|->s5, s19|->s7, s19|->s8, s19|->s9, s19|->s11, s19|->s14, s19|->s15, s19|->s16, s19|->s17, s20|->s1, s20|->s2, s20|->s3, s20|->s5, s20|->s9, s20|->s10, s20|->s14, s20|->s16, s20|->s18, s20|->s19, s21|->s2, s21|->s6, s21|->s10, s21|->s11, s21|->s12, s21|->s14, s21|->s19, s21|->s20, s22|->s2, s22|->s4, s22|->s6, s22|->s7, s22|->s8, s22|->s9, s22|->s11, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s17, s22|->s18, s22|->s20, s22|->s21, s23|->s0, s23|->s1, s23|->s3, s23|->s4, s23|->s5, s23|->s6, s23|->s8, s23|->s12, s23|->s13, s23|->s18, s23|->s19, s23|->s20, s23|->s21, s23|->s22, s24|->s2, s24|->s3, s24|->s4, s24|->s5, s24|->s6, s24|->s9, s24|->s10, s24|->s12, s24|->s15, s24|->s16, s24|->s21, s24|->s23} &
    e_res={r1|->r0, r2|->r0, r3|->r0, r5|->r1, r5|->r2, r6|->r2, r7|->r1, r7|->r4, r7|->r6, r8|->r2, r8|->r4, r8|->r5, r8|->r6, r9|->r1, r9|->r3, r9|->r4, r9|->r6, r9|->r7, r10|->r1, r10|->r3, r10|->r4, r10|->r7, r10|->r9, r11|->r1, r11|->r2, r11|->r4, r11|->r5, r11|->r6, r11|->r7, r11|->r9, r11|->r10, r12|->r1, r12|->r2, r12|->r4, r12|->r5, r12|->r6, r12|->r8, r12|->r9, r13|->r7, r13|->r10, r13|->r11, r13|->r12, r14|->r0, r14|->r2, r14|->r6, r14|->r8, r14|->r11, r14|->r12, r14|->r13, r15|->r0, r15|->r1, r15|->r2, r15|->r5, r15|->r7, r15|->r8, r15|->r9, r15|->r11, r15|->r12, r15|->r13, r16|->r1, r16|->r2, r16|->r3, r16|->r5, r16|->r7, r16|->r8, r16|->r12, r16|->r15, r17|->r1, r17|->r3, r17|->r4, r17|->r6, r17|->r7, r17|->r8, r17|->r12, r17|->r13, r17|->r14, r17|->r15, r17|->r16, r18|->r0, r18|->r4, r18|->r5, r18|->r8, r18|->r11, r18|->r16, r18|->r17, r19|->r0, r19|->r1, r19|->r3, r19|->r5, r19|->r7, r19|->r8, r19|->r15, r19|->r18, r20|->r3, r20|->r4, r20|->r6, r20|->r9, r20|->r10, r20|->r13, r20|->r14, r20|->r16, r20|->r18, r20|->r19, r21|->r0, r21|->r1, r21|->r2, r21|->r3, r21|->r4, r21|->r5, r21|->r8, r21|->r9, r21|->r10, r21|->r12, r21|->r13, r21|->r14, r21|->r15, r21|->r18, r22|->r1, r22|->r2, r22|->r4, r22|->r5, r22|->r7, r22|->r8, r22|->r9, r22|->r10, r22|->r11, r22|->r19, r23|->r0, r23|->r1, r23|->r3, r23|->r5, r23|->r7, r23|->r14, r23|->r16, r23|->r18, r23|->r19, r24|->r0, r24|->r1, r24|->r3, r24|->r5, r24|->r6, r24|->r7, r24|->r9, r24|->r10, r24|->r11, r24|->r12, r24|->r13, r24|->r15, r24|->r16, r24|->r18, r24|->r21} &
    rules={rule0|->(rec(su:s9,re:r13,mo:per,pr: 4,co:{c3,c2})), rule1|->(rec(su:s10,re:r16,mo:per,pr: 1,co:{c0,c2,c7,c6,c1,c9,c5})), rule2|->(rec(su:s13,re:r21,mo:per,pr: 1,co:{c7,c6,c2,c4})), rule3|->(rec(su:s21,re:r14,mo:per,pr: 1,co:{c1,c9,c8,c3})), rule4|->(rec(su:s11,re:r13,mo:per,pr: 0,co:{c1,c9,c5,c4})), rule5|->(rec(su:s13,re:r4,mo:pro,pr: 4,co:{c8})), rule6|->(rec(su:s14,re:r3,mo:per,pr: 2,co:{c2,c7,c9})), rule7|->(rec(su:s3,re:r13,mo:pro,pr: 1,co:{c4,c6,c8})), rule8|->(rec(su:s18,re:r10,mo:pro,pr: 2,co:{c3,c4,c6,c1,c8,c7})), rule9|->(rec(su:s17,re:r10,mo:pro,pr: 0,co:{c6})), rule10|->(rec(su:s2,re:r9,mo:per,pr: 0,co:{c9,c3,c5,c2,c0,c4})), rule11|->(rec(su:s11,re:r7,mo:per,pr: 1,co:{c7,c8,c5,c4,c6,c1})), rule12|->(rec(su:s5,re:r8,mo:per,pr: 2,co:{c9,c8,c7,c1,c6,c5,c4}))}

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