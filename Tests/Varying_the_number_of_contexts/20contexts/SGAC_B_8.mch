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
    CONTEXT={c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19};
    /*subject vertex type*/
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29};
    /*rule type*/
    RULE_T={rule0, rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8, rule9, rule10, rule11};
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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s3|->s0, s3|->s1, s4|->s1, s5|->s1, s5|->s2, s6|->s0, s6|->s4, s7|->s1, s7|->s2, s7|->s3, s7|->s4, s7|->s6, s8|->s0, s8|->s1, s8|->s2, s8|->s5, s8|->s6, s8|->s7, s9|->s0, s9|->s3, s9|->s4, s9|->s6, s9|->s8, s10|->s0, s10|->s3, s10|->s5, s10|->s6, s10|->s7, s10|->s8, s11|->s0, s11|->s1, s11|->s2, s11|->s4, s11|->s10, s12|->s2, s12|->s3, s12|->s5, s12|->s8, s12|->s9, s13|->s2, s13|->s3, s13|->s4, s13|->s10, s14|->s0, s14|->s1, s14|->s2, s14|->s3, s14|->s6, s14|->s7, s14|->s11, s14|->s12, s14|->s13, s15|->s0, s15|->s1, s15|->s2, s15|->s4, s15|->s6, s15|->s9, s15|->s11, s15|->s12, s15|->s13, s16|->s2, s16|->s4, s16|->s5, s16|->s6, s16|->s8, s16|->s13, s16|->s14, s17|->s0, s17|->s1, s17|->s2, s17|->s4, s17|->s5, s17|->s7, s17|->s9, s17|->s10, s17|->s11, s17|->s14, s17|->s16, s18|->s0, s18|->s1, s18|->s6, s18|->s7, s18|->s8, s18|->s9, s18|->s10, s18|->s11, s18|->s12, s18|->s13, s19|->s2, s19|->s3, s19|->s5, s19|->s7, s19|->s13, s19|->s14, s19|->s16, s20|->s1, s20|->s2, s20|->s3, s20|->s4, s20|->s5, s20|->s6, s20|->s7, s20|->s8, s20|->s9, s20|->s10, s20|->s12, s21|->s1, s21|->s2, s21|->s3, s21|->s4, s21|->s6, s21|->s7, s21|->s8, s21|->s9, s21|->s11, s21|->s12, s21|->s13, s21|->s19, s22|->s0, s22|->s1, s22|->s2, s22|->s7, s22|->s8, s22|->s9, s22|->s11, s22|->s15, s22|->s18, s22|->s19, s23|->s0, s23|->s1, s23|->s3, s23|->s5, s23|->s9, s23|->s10, s23|->s12, s23|->s13, s23|->s14, s23|->s17, s23|->s19, s23|->s21, s23|->s22, s24|->s1, s24|->s2, s24|->s3, s24|->s4, s24|->s7, s24|->s8, s24|->s10, s24|->s13, s24|->s16, s24|->s17, s24|->s21, s24|->s22, s25|->s1, s25|->s4, s25|->s5, s25|->s13, s25|->s16, s25|->s17, s25|->s18, s25|->s19, s25|->s20, s25|->s22, s26|->s1, s26|->s2, s26|->s8, s26|->s11, s26|->s12, s26|->s15, s26|->s16, s26|->s19, s26|->s21, s26|->s23, s27|->s2, s27|->s4, s27|->s7, s27|->s8, s27|->s14, s27|->s15, s27|->s16, s27|->s18, s27|->s21, s27|->s22, s27|->s23, s27|->s24, s27|->s26, s28|->s1, s28|->s2, s28|->s3, s28|->s8, s28|->s10, s28|->s11, s28|->s13, s28|->s15, s28|->s16, s28|->s18, s28|->s21, s28|->s22, s28|->s25, s29|->s0, s29|->s3, s29|->s4, s29|->s5, s29|->s6, s29|->s7, s29|->s8, s29|->s9, s29|->s15, s29|->s16, s29|->s17, s29|->s20, s29|->s22, s29|->s23} &
    e_res={r1|->r0, r2|->r0, r3|->r0, r4|->r0, r4|->r1, r5|->r0, r5|->r1, r6|->r0, r6|->r1, r6|->r2, r6|->r3, r7|->r6, r8|->r0, r8|->r1, r8|->r6, r9|->r1, r9|->r2, r9|->r3, r9|->r5, r9|->r6, r9|->r7, r9|->r8, r10|->r0, r10|->r4, r10|->r6, r10|->r9, r11|->r0, r11|->r3, r11|->r5, r11|->r8, r11|->r9, r12|->r0, r12|->r5, r12|->r7, r12|->r8, r12|->r10, r13|->r2, r13|->r7, r13|->r10, r14|->r0, r14|->r1, r14|->r2, r14|->r4, r14|->r5, r14|->r8, r15|->r4, r15|->r5, r15|->r8, r15|->r10, r15|->r11, r15|->r12, r15|->r13, r15|->r14, r16|->r2, r16|->r4, r16|->r5, r16|->r7, r16|->r8, r16|->r9, r16|->r10, r16|->r11, r16|->r15, r17|->r1, r17|->r4, r17|->r5, r17|->r6, r17|->r7, r17|->r9, r17|->r10, r17|->r12, r17|->r14, r17|->r15, r17|->r16, r18|->r1, r18|->r5, r18|->r7, r18|->r9, r18|->r16, r19|->r1, r19|->r4, r19|->r5, r19|->r6, r19|->r7, r19|->r8, r19|->r10, r19|->r11, r19|->r13, r19|->r14, r19|->r15, r19|->r16, r20|->r0, r20|->r1, r20|->r3, r20|->r4, r20|->r6, r20|->r8, r20|->r9, r20|->r14, r20|->r17, r20|->r18, r21|->r1, r21|->r4, r21|->r5, r21|->r6, r21|->r7, r21|->r9, r21|->r11, r21|->r12, r21|->r13, r21|->r15, r21|->r16, r21|->r17, r21|->r18, r21|->r20, r22|->r2, r22|->r3, r22|->r8, r22|->r12, r22|->r13, r22|->r19, r22|->r20, r23|->r0, r23|->r5, r23|->r7, r23|->r8, r23|->r9, r23|->r11, r23|->r13, r23|->r14, r23|->r15, r23|->r22, r24|->r0, r24|->r4, r24|->r6, r24|->r7, r24|->r9, r24|->r11, r24|->r15, r24|->r16, r24|->r17, r24|->r18, r24|->r20, r25|->r0, r25|->r1, r25|->r2, r25|->r3, r25|->r7, r25|->r8, r25|->r10, r25|->r11, r25|->r12, r25|->r15, r25|->r16, r25|->r17, r25|->r18, r25|->r20, r25|->r22, r25|->r23, r25|->r24, r26|->r0, r26|->r4, r26|->r5, r26|->r8, r26|->r10, r26|->r12, r26|->r16, r26|->r17, r26|->r18, r26|->r21, r26|->r22, r26|->r25, r27|->r0, r27|->r1, r27|->r5, r27|->r7, r27|->r8, r27|->r9, r27|->r11, r27|->r12, r27|->r14, r27|->r16, r27|->r17, r27|->r19, r27|->r20, r27|->r22, r27|->r23, r27|->r24, r27|->r25, r28|->r1, r28|->r2, r28|->r3, r28|->r4, r28|->r6, r28|->r8, r28|->r11, r28|->r13, r28|->r14, r28|->r15, r28|->r16, r28|->r18, r28|->r19, r28|->r20, r28|->r21, r28|->r23, r28|->r26, r29|->r2, r29|->r4, r29|->r6, r29|->r7, r29|->r8, r29|->r11, r29|->r13, r29|->r16, r29|->r17, r29|->r19, r29|->r20, r29|->r21, r29|->r23, r29|->r24, r29|->r27} &
    rules={rule0|->(rec(su:s13,re:r19,mo:pro,pr: 3,co:{c14,c0})), rule1|->(rec(su:s3,re:r12,mo:per,pr: 2,co:{c17,c1,c18,c8,c2,c5,c12,c0})), rule2|->(rec(su:s9,re:r28,mo:pro,pr: 3,co:{c16})), rule3|->(rec(su:s4,re:r27,mo:per,pr: 3,co:{c17,c0,c15,c11,c1,c5,c7,c6,c2,c18,c3})), rule4|->(rec(su:s3,re:r7,mo:pro,pr: 0,co:{c15,c3,c5,c6,c17,c9,c0,c2,c11})), rule5|->(rec(su:s3,re:r14,mo:pro,pr: 2,co:{c4,c6,c14,c18})), rule6|->(rec(su:s17,re:r22,mo:pro,pr: 1,co:{c4,c8,c5,c6,c3,c17,c7,c18,c9,c1,c13})), rule7|->(rec(su:s15,re:r19,mo:per,pr: 1,co:{c7,c2,c4,c10,c8,c0,c13,c16})), rule8|->(rec(su:s26,re:r8,mo:pro,pr: 0,co:{c16,c11,c13,c8,c15,c3,c1,c12})), rule9|->(rec(su:s1,re:r21,mo:pro,pr: 3,co:{c4,c0,c2,c6,c5,c9,c16})), rule10|->(rec(su:s7,re:r22,mo:per,pr: 2,co:{c17,c14,c6,c8,c2,c11,c7,c12,c19,c9,c10,c16,c5})), rule11|->(rec(su:s22,re:r3,mo:pro,pr: 2,co:{c12,c13,c10,c14,c3,c0,c9,c19,c15,c8,c5}))}

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