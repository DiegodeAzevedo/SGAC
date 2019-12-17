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
    e_sub={s1|->s0, s2|->s0, s3|->s0, s3|->s1, s3|->s2, s4|->s0, s4|->s2, s5|->s0, s5|->s4, s6|->s1, s6|->s4, s7|->s0, s7|->s4, s7|->s5, s8|->s2, s8|->s3, s8|->s4, s9|->s0, s9|->s2, s9|->s3, s9|->s6, s9|->s7, s9|->s8, s10|->s3, s10|->s4, s10|->s6, s10|->s7, s10|->s8, s11|->s0, s11|->s1, s11|->s4, s11|->s5, s11|->s6, s11|->s7, s11|->s9, s12|->s0, s12|->s1, s12|->s2, s12|->s3, s12|->s4, s12|->s6, s12|->s7, s13|->s2, s13|->s3, s13|->s5, s13|->s7, s13|->s10, s13|->s11, s14|->s1, s14|->s3, s14|->s4, s14|->s5, s14|->s6, s14|->s7, s14|->s9, s14|->s13, s15|->s0, s15|->s2, s15|->s4, s15|->s6, s15|->s8, s15|->s9, s15|->s10, s15|->s13, s16|->s0, s16|->s2, s16|->s3, s16|->s4, s16|->s7, s16|->s8, s16|->s10, s16|->s11, s16|->s12, s16|->s15, s17|->s6, s17|->s7, s17|->s8, s17|->s9, s17|->s10, s17|->s11, s17|->s13, s17|->s16, s18|->s0, s18|->s3, s18|->s6, s18|->s7, s18|->s8, s18|->s9, s18|->s13, s18|->s14, s18|->s15, s18|->s17, s19|->s2, s19|->s3, s19|->s6, s19|->s7, s19|->s8, s19|->s9, s19|->s10, s19|->s11, s19|->s13, s19|->s15, s19|->s16, s19|->s17, s19|->s18, s20|->s1, s20|->s4, s20|->s9, s20|->s10, s20|->s14, s20|->s17, s20|->s18, s21|->s0, s21|->s1, s21|->s2, s21|->s4, s21|->s5, s21|->s6, s21|->s8, s21|->s15, s21|->s16, s21|->s18, s21|->s20, s22|->s1, s22|->s2, s22|->s3, s22|->s4, s22|->s5, s22|->s7, s22|->s8, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s18, s22|->s20, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s4, s23|->s7, s23|->s9, s23|->s14, s23|->s16, s23|->s18, s23|->s20, s23|->s21, s23|->s22, s24|->s2, s24|->s3, s24|->s4, s24|->s5, s24|->s6, s24|->s8, s24|->s9, s24|->s10, s24|->s11, s24|->s12, s24|->s17, s24|->s22, s24|->s23, s25|->s1, s25|->s2, s25|->s3, s25|->s5, s25|->s6, s25|->s8, s25|->s9, s25|->s12, s25|->s13, s25|->s14, s25|->s16, s25|->s17, s25|->s18, s25|->s19, s25|->s20, s25|->s22, s26|->s0, s26|->s4, s26|->s6, s26|->s8, s26|->s11, s26|->s15, s26|->s16, s26|->s19, s26|->s22, s27|->s0, s27|->s2, s27|->s4, s27|->s8, s27|->s9, s27|->s11, s27|->s13, s27|->s14, s27|->s16, s27|->s17, s27|->s18, s27|->s25, s27|->s26, s28|->s3, s28|->s4, s28|->s6, s28|->s18, s28|->s20, s28|->s21, s28|->s22, s28|->s24, s28|->s25, s29|->s0, s29|->s2, s29|->s3, s29|->s6, s29|->s11, s29|->s12, s29|->s13, s29|->s14, s29|->s19, s29|->s20, s29|->s23, s29|->s25, s29|->s27, s29|->s28} &
    e_res={r1|->r0, r2|->r1, r3|->r0, r3|->r2, r4|->r3, r6|->r1, r6|->r2, r6|->r4, r7|->r0, r7|->r2, r7|->r3, r7|->r4, r7|->r5, r8|->r0, r8|->r1, r8|->r3, r8|->r5, r8|->r6, r8|->r7, r9|->r0, r9|->r3, r9|->r4, r9|->r5, r9|->r6, r9|->r8, r10|->r2, r10|->r4, r10|->r6, r10|->r7, r10|->r8, r11|->r2, r11|->r4, r11|->r6, r11|->r7, r11|->r8, r11|->r10, r12|->r3, r12|->r4, r12|->r6, r12|->r7, r12|->r9, r12|->r10, r13|->r2, r13|->r5, r13|->r8, r13|->r10, r13|->r11, r14|->r1, r14|->r2, r14|->r5, r14|->r9, r14|->r11, r14|->r12, r15|->r0, r15|->r3, r15|->r6, r15|->r8, r15|->r9, r15|->r10, r15|->r11, r15|->r13, r16|->r0, r16|->r1, r16|->r4, r16|->r6, r16|->r7, r16|->r8, r16|->r9, r16|->r10, r16|->r15, r17|->r1, r17|->r2, r17|->r3, r17|->r4, r17|->r7, r17|->r8, r17|->r14, r18|->r1, r18|->r3, r18|->r5, r18|->r6, r18|->r9, r18|->r11, r18|->r12, r18|->r15, r18|->r16, r19|->r1, r19|->r6, r19|->r9, r19|->r10, r19|->r11, r19|->r13, r19|->r16, r20|->r1, r20|->r2, r20|->r4, r20|->r6, r20|->r7, r20|->r9, r20|->r12, r20|->r13, r20|->r17, r21|->r0, r21|->r2, r21|->r7, r21|->r9, r21|->r12, r21|->r17, r21|->r20, r22|->r6, r22|->r9, r22|->r11, r22|->r13, r22|->r18, r22|->r21, r23|->r0, r23|->r1, r23|->r3, r23|->r5, r23|->r6, r23|->r7, r23|->r8, r23|->r10, r23|->r13, r23|->r15, r23|->r16, r23|->r18, r23|->r19, r24|->r0, r24|->r1, r24|->r4, r24|->r5, r24|->r14, r24|->r15, r24|->r16, r24|->r17, r24|->r18, r24|->r19, r24|->r20, r24|->r21, r24|->r22, r24|->r23, r25|->r0, r25|->r4, r25|->r6, r25|->r14, r25|->r16, r25|->r17, r25|->r19, r25|->r21, r25|->r22, r25|->r24, r26|->r0, r26|->r1, r26|->r3, r26|->r6, r26|->r11, r26|->r12, r26|->r15, r26|->r16, r26|->r19, r26|->r21, r26|->r24, r27|->r0, r27|->r1, r27|->r2, r27|->r3, r27|->r4, r27|->r5, r27|->r7, r27|->r10, r27|->r11, r27|->r14, r27|->r15, r27|->r17, r27|->r25, r28|->r1, r28|->r3, r28|->r7, r28|->r12, r28|->r14, r28|->r15, r28|->r16, r28|->r18, r28|->r19, r28|->r20, r28|->r25, r28|->r26, r28|->r27, r29|->r2, r29|->r4, r29|->r7, r29|->r10, r29|->r12, r29|->r13, r29|->r14, r29|->r16, r29|->r21, r29|->r22, r29|->r23} &
    rules={rule0|->(rec(su:s27,re:r24,mo:pro,pr: 4,co:{c10,c18,c15,c3,c13,c16,c11,c0,c9,c1})), rule1|->(rec(su:s18,re:r8,mo:pro,pr: 4,co:{c10,c4,c14,c6,c13,c17,c9,c3,c8,c19,c5,c2})), rule2|->(rec(su:s11,re:r25,mo:per,pr: 4,co:{c16,c1,c7})), rule3|->(rec(su:s21,re:r3,mo:pro,pr: 4,co:{c3,c8,c1,c10,c13,c16,c0,c7,c11,c15,c4,c18})), rule4|->(rec(su:s0,re:r7,mo:per,pr: 0,co:{c2,c11,c14,c19,c16,c0,c4,c9,c6,c8,c17,c13,c10})), rule5|->(rec(su:s1,re:r8,mo:pro,pr: 2,co:{c17,c16,c12,c7,c1})), rule6|->(rec(su:s17,re:r1,mo:per,pr: 2,co:{c2,c8,c10,c15,c4})), rule7|->(rec(su:s20,re:r28,mo:pro,pr: 3,co:{c1,c17,c4,c8,c7,c13})), rule8|->(rec(su:s10,re:r0,mo:pro,pr: 3,co:{c4,c12,c19,c6,c13,c5,c9,c14,c7,c17,c3,c2,c15})), rule9|->(rec(su:s17,re:r21,mo:per,pr: 0,co:{c6,c5,c11,c14,c1})), rule10|->(rec(su:s19,re:r21,mo:pro,pr: 3,co:{c0,c7,c15,c11,c16,c8,c12,c10,c4})), rule11|->(rec(su:s9,re:r23,mo:pro,pr: 0,co:{c13,c8,c18}))}

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