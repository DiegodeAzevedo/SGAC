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
    CONTEXT={c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29};
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
    e_sub={s1|->s0, s3|->s0, s4|->s2, s5|->s0, s5|->s1, s5|->s2, s5|->s3, s5|->s4, s6|->s0, s6|->s3, s7|->s2, s7|->s3, s7|->s4, s7|->s5, s7|->s6, s8|->s1, s8|->s2, s8|->s7, s9|->s0, s9|->s2, s9|->s5, s9|->s6, s9|->s7, s9|->s8, s10|->s0, s10|->s1, s10|->s2, s10|->s5, s10|->s6, s10|->s7, s10|->s9, s11|->s0, s11|->s3, s11|->s7, s11|->s9, s11|->s10, s12|->s1, s12|->s2, s12|->s4, s12|->s7, s12|->s9, s12|->s10, s13|->s1, s13|->s2, s13|->s3, s13|->s4, s13|->s8, s13|->s9, s13|->s10, s14|->s2, s14|->s4, s14|->s7, s14|->s8, s15|->s1, s15|->s2, s15|->s6, s15|->s7, s15|->s8, s15|->s11, s15|->s13, s15|->s14, s16|->s0, s16|->s1, s16|->s4, s16|->s5, s16|->s7, s16|->s9, s16|->s12, s16|->s14, s17|->s5, s17|->s7, s17|->s9, s17|->s11, s17|->s12, s18|->s1, s18|->s2, s18|->s4, s18|->s6, s18|->s7, s18|->s9, s18|->s11, s18|->s13, s18|->s14, s19|->s1, s19|->s2, s19|->s3, s19|->s10, s19|->s13, s19|->s15, s19|->s16, s19|->s17, s19|->s18, s20|->s0, s20|->s1, s20|->s4, s20|->s6, s20|->s9, s20|->s12, s20|->s14, s20|->s15, s20|->s17, s21|->s1, s21|->s3, s21|->s4, s21|->s6, s21|->s9, s21|->s10, s21|->s12, s21|->s13, s21|->s14, s21|->s15, s21|->s16, s21|->s20, s22|->s0, s22|->s1, s22|->s2, s22|->s3, s22|->s5, s22|->s6, s22|->s8, s22|->s10, s22|->s11, s22|->s13, s22|->s14, s22|->s15, s22|->s20, s23|->s0, s23|->s2, s23|->s4, s23|->s5, s23|->s6, s23|->s8, s23|->s9, s23|->s13, s23|->s19, s23|->s21, s23|->s22, s24|->s0, s24|->s3, s24|->s4, s24|->s5, s24|->s7, s24|->s8, s24|->s11, s24|->s12, s24|->s13, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s21, s24|->s22, s25|->s0, s25|->s2, s25|->s4, s25|->s7, s25|->s8, s25|->s10, s25|->s11, s25|->s14, s25|->s15, s25|->s16, s25|->s17, s25|->s19, s25|->s20, s25|->s21, s25|->s23, s26|->s0, s26|->s2, s26|->s3, s26|->s5, s26|->s6, s26|->s9, s26|->s10, s26|->s11, s26|->s12, s26|->s15, s26|->s16, s26|->s17, s26|->s18, s26|->s23, s26|->s24, s26|->s25, s27|->s0, s27|->s1, s27|->s2, s27|->s3, s27|->s5, s27|->s6, s27|->s8, s27|->s11, s27|->s12, s27|->s13, s27|->s15, s27|->s16, s27|->s17, s27|->s19, s28|->s0, s28|->s1, s28|->s4, s28|->s5, s28|->s6, s28|->s7, s28|->s10, s28|->s12, s28|->s14, s28|->s15, s28|->s20, s28|->s23, s28|->s24, s28|->s26, s28|->s27, s29|->s0, s29|->s1, s29|->s2, s29|->s10, s29|->s11, s29|->s13, s29|->s14, s29|->s21, s29|->s23, s29|->s24, s29|->s25, s29|->s27, s29|->s28} &
    e_res={r2|->r0, r3|->r2, r4|->r0, r5|->r3, r6|->r0, r6|->r1, r6|->r2, r6|->r3, r6|->r4, r7|->r2, r7|->r4, r7|->r6, r8|->r3, r8|->r4, r8|->r5, r9|->r0, r9|->r2, r9|->r4, r9|->r7, r10|->r3, r10|->r4, r10|->r8, r10|->r9, r11|->r0, r11|->r5, r11|->r7, r12|->r0, r12|->r1, r12|->r2, r12|->r3, r12|->r6, r12|->r7, r12|->r9, r12|->r11, r13|->r1, r13|->r2, r13|->r5, r13|->r10, r13|->r11, r13|->r12, r14|->r2, r14|->r7, r14|->r8, r14|->r10, r14|->r11, r15|->r1, r15|->r3, r15|->r5, r15|->r6, r15|->r10, r15|->r14, r16|->r0, r16|->r3, r16|->r4, r16|->r8, r16|->r9, r16|->r10, r16|->r11, r16|->r14, r17|->r0, r17|->r3, r17|->r7, r17|->r8, r17|->r12, r17|->r16, r18|->r1, r18|->r3, r18|->r8, r18|->r9, r18|->r10, r18|->r12, r18|->r13, r18|->r17, r19|->r2, r19|->r3, r19|->r5, r19|->r9, r19|->r11, r19|->r13, r19|->r14, r19|->r15, r19|->r17, r19|->r18, r20|->r1, r20|->r4, r20|->r5, r20|->r9, r20|->r11, r20|->r14, r20|->r15, r20|->r16, r20|->r18, r20|->r19, r21|->r0, r21|->r2, r21|->r4, r21|->r5, r21|->r6, r21|->r7, r21|->r9, r21|->r10, r21|->r11, r21|->r12, r21|->r13, r21|->r15, r21|->r16, r21|->r18, r21|->r20, r22|->r1, r22|->r2, r22|->r3, r22|->r4, r22|->r5, r22|->r6, r22|->r8, r22|->r12, r22|->r15, r22|->r17, r22|->r21, r23|->r0, r23|->r3, r23|->r5, r23|->r6, r23|->r7, r23|->r9, r23|->r12, r23|->r15, r23|->r18, r23|->r21, r23|->r22, r24|->r1, r24|->r2, r24|->r4, r24|->r8, r24|->r10, r24|->r11, r24|->r13, r24|->r18, r24|->r19, r24|->r20, r24|->r23, r25|->r5, r25|->r7, r25|->r10, r25|->r12, r25|->r13, r25|->r15, r25|->r16, r25|->r17, r25|->r20, r25|->r21, r25|->r23, r25|->r24, r26|->r0, r26|->r1, r26|->r3, r26|->r5, r26|->r6, r26|->r9, r26|->r10, r26|->r12, r26|->r15, r26|->r16, r26|->r17, r26|->r18, r26|->r19, r26|->r21, r26|->r22, r26|->r23, r26|->r25, r27|->r0, r27|->r1, r27|->r4, r27|->r5, r27|->r9, r27|->r10, r27|->r15, r27|->r18, r27|->r19, r27|->r20, r27|->r22, r27|->r26, r28|->r5, r28|->r6, r28|->r8, r28|->r9, r28|->r10, r28|->r11, r28|->r12, r28|->r15, r28|->r16, r28|->r17, r28|->r18, r28|->r19, r28|->r21, r28|->r22, r28|->r23, r28|->r24, r28|->r25, r28|->r26, r28|->r27, r29|->r0, r29|->r1, r29|->r5, r29|->r7, r29|->r12, r29|->r13, r29|->r14, r29|->r15, r29|->r17, r29|->r18, r29|->r19, r29|->r20, r29|->r21, r29|->r26, r29|->r28} &
    rules={rule0|->(rec(su:s18,re:r8,mo:pro,pr: 0,co:{c25,c12,c19,c24,c17,c14,c7,c6,c3,c22,c18})), rule1|->(rec(su:s2,re:r5,mo:per,pr: 2,co:{c12,c28,c1,c17,c21,c13})), rule2|->(rec(su:s14,re:r0,mo:pro,pr: 2,co:{c14,c19,c4,c11,c12,c23,c1,c0,c6,c9,c2,c3,c24,c13,c22})), rule3|->(rec(su:s11,re:r15,mo:per,pr: 1,co:{c2,c13,c12,c20,c3,c7,c6,c27,c26,c25})), rule4|->(rec(su:s25,re:r12,mo:pro,pr: 0,co:{c25,c16,c0,c2})), rule5|->(rec(su:s7,re:r2,mo:pro,pr: 0,co:{c1,c15,c3,c29,c18,c10,c16,c20,c22,c13,c2,c27,c9,c25,c11,c17,c5,c26})), rule6|->(rec(su:s8,re:r13,mo:per,pr: 1,co:{c5,c22,c23,c18,c27,c14,c4,c21,c17,c24,c13,c29,c9,c15,c7,c25,c26,c20})), rule7|->(rec(su:s7,re:r25,mo:pro,pr: 4,co:{c13,c0,c19,c5,c18,c24,c29,c16,c3,c28,c25,c12,c11,c22})), rule8|->(rec(su:s25,re:r19,mo:pro,pr: 2,co:{c18,c23,c29,c24,c28,c2,c16,c5,c20,c14,c8,c12,c6,c10,c3,c1,c25})), rule9|->(rec(su:s2,re:r19,mo:per,pr: 1,co:{c2,c4,c28,c6,c7,c11,c21,c10,c9,c8})), rule10|->(rec(su:s28,re:r1,mo:pro,pr: 4,co:{c5,c3,c14,c18,c16,c23,c1,c26,c6,c28,c19,c17,c15,c25,c20,c4,c8,c10})), rule11|->(rec(su:s15,re:r11,mo:per,pr: 2,co:{c7,c12,c6,c15,c16,c19,c25,c14,c20,c26,c28,c21}))}

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