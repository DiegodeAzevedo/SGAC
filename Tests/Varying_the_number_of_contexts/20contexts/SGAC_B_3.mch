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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s3|->s0, s3|->s1, s4|->s0, s4|->s3, s5|->s0, s5|->s1, s5|->s3, s5|->s4, s6|->s2, s6|->s5, s7|->s1, s7|->s3, s7|->s4, s8|->s0, s8|->s5, s8|->s7, s9|->s0, s9|->s2, s9|->s5, s9|->s8, s10|->s2, s10|->s8, s11|->s1, s11|->s7, s12|->s0, s12|->s2, s12|->s4, s12|->s6, s12|->s7, s12|->s8, s12|->s9, s12|->s10, s13|->s0, s13|->s1, s13|->s3, s13|->s7, s13|->s8, s13|->s9, s13|->s11, s13|->s12, s14|->s0, s14|->s1, s14|->s3, s14|->s6, s14|->s8, s14|->s9, s14|->s10, s14|->s13, s15|->s3, s15|->s4, s15|->s7, s15|->s9, s15|->s12, s15|->s13, s16|->s0, s16|->s4, s16|->s7, s16|->s8, s16|->s10, s16|->s12, s16|->s14, s16|->s15, s17|->s0, s17|->s3, s17|->s5, s17|->s13, s17|->s14, s17|->s15, s18|->s1, s18|->s3, s18|->s4, s18|->s6, s18|->s7, s18|->s11, s18|->s13, s18|->s14, s18|->s17, s19|->s0, s19|->s1, s19|->s3, s19|->s5, s19|->s6, s19|->s8, s19|->s10, s19|->s11, s19|->s12, s19|->s14, s20|->s1, s20|->s3, s20|->s4, s20|->s7, s20|->s8, s20|->s9, s20|->s14, s20|->s15, s20|->s17, s20|->s18, s20|->s19, s21|->s4, s21|->s6, s21|->s9, s21|->s10, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s16, s21|->s18, s21|->s19, s22|->s1, s22|->s2, s22|->s4, s22|->s5, s22|->s6, s22|->s8, s22|->s12, s22|->s16, s22|->s17, s22|->s21, s23|->s1, s23|->s2, s23|->s3, s23|->s7, s23|->s8, s23|->s15, s23|->s16, s23|->s18, s23|->s19, s23|->s20, s23|->s22, s24|->s0, s24|->s1, s24|->s3, s24|->s5, s24|->s6, s24|->s7, s24|->s8, s24|->s9, s24|->s10, s24|->s13, s24|->s15, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s20, s25|->s1, s25|->s3, s25|->s4, s25|->s6, s25|->s7, s25|->s9, s25|->s10, s25|->s11, s25|->s13, s25|->s14, s25|->s16, s25|->s18, s25|->s19, s25|->s22, s25|->s23, s26|->s1, s26|->s2, s26|->s5, s26|->s6, s26|->s10, s26|->s11, s26|->s12, s26|->s13, s26|->s16, s26|->s18, s26|->s20, s26|->s22, s26|->s24, s27|->s1, s27|->s3, s27|->s6, s27|->s7, s27|->s10, s27|->s11, s27|->s14, s27|->s15, s27|->s17, s27|->s20, s27|->s24, s27|->s26, s28|->s0, s28|->s1, s28|->s2, s28|->s3, s28|->s4, s28|->s5, s28|->s6, s28|->s7, s28|->s9, s28|->s13, s28|->s14, s28|->s15, s28|->s16, s28|->s18, s28|->s21, s28|->s22, s28|->s24, s28|->s26, s28|->s27, s29|->s0, s29|->s1, s29|->s3, s29|->s5, s29|->s6, s29|->s7, s29|->s10, s29|->s17, s29|->s19, s29|->s20, s29|->s21, s29|->s23, s29|->s27} &
    e_res={r1|->r0, r4|->r0, r4|->r2, r5|->r1, r5|->r2, r5|->r3, r5|->r4, r6|->r0, r6|->r3, r6|->r4, r6|->r5, r7|->r0, r7|->r1, r7|->r3, r7|->r6, r8|->r2, r8|->r4, r8|->r6, r8|->r7, r9|->r1, r9|->r2, r9|->r4, r9|->r5, r9|->r6, r10|->r0, r10|->r2, r10|->r7, r10|->r9, r11|->r0, r11|->r5, r11|->r7, r11|->r9, r11|->r10, r12|->r0, r12|->r2, r12|->r6, r12|->r8, r12|->r10, r13|->r0, r13|->r1, r13|->r5, r13|->r6, r13|->r10, r13|->r11, r13|->r12, r14|->r1, r14|->r3, r14|->r8, r14|->r9, r14|->r10, r15|->r0, r15|->r2, r15|->r3, r15|->r4, r15|->r6, r15|->r7, r15|->r8, r15|->r9, r15|->r12, r15|->r14, r16|->r0, r16|->r1, r16|->r3, r16|->r4, r16|->r5, r16|->r6, r16|->r7, r16|->r8, r16|->r11, r16|->r12, r16|->r13, r17|->r0, r17|->r1, r17|->r2, r17|->r9, r17|->r13, r17|->r15, r17|->r16, r18|->r0, r18|->r4, r18|->r6, r18|->r7, r18|->r8, r18|->r10, r18|->r11, r18|->r14, r18|->r15, r18|->r16, r18|->r17, r19|->r3, r19|->r4, r19|->r5, r19|->r6, r19|->r7, r19|->r10, r19|->r12, r19|->r16, r19|->r17, r20|->r0, r20|->r1, r20|->r2, r20|->r5, r20|->r6, r20|->r7, r20|->r9, r20|->r10, r20|->r11, r20|->r13, r20|->r17, r20|->r18, r21|->r0, r21|->r1, r21|->r4, r21|->r5, r21|->r8, r21|->r9, r21|->r10, r21|->r14, r21|->r15, r21|->r16, r21|->r18, r21|->r19, r21|->r20, r22|->r0, r22|->r1, r22|->r2, r22|->r3, r22|->r4, r22|->r9, r22|->r10, r22|->r16, r22|->r18, r22|->r19, r22|->r20, r23|->r1, r23|->r2, r23|->r3, r23|->r7, r23|->r8, r23|->r10, r23|->r11, r23|->r12, r23|->r17, r23|->r18, r23|->r19, r23|->r20, r23|->r22, r24|->r0, r24|->r3, r24|->r5, r24|->r7, r24|->r8, r24|->r9, r24|->r12, r24|->r13, r24|->r14, r24|->r16, r24|->r18, r24|->r19, r24|->r21, r24|->r23, r25|->r0, r25|->r1, r25|->r2, r25|->r4, r25|->r6, r25|->r7, r25|->r11, r25|->r14, r25|->r15, r25|->r18, r25|->r20, r25|->r23, r26|->r2, r26|->r3, r26|->r4, r26|->r5, r26|->r6, r26|->r8, r26|->r10, r26|->r11, r26|->r14, r26|->r15, r26|->r16, r26|->r21, r26|->r22, r26|->r23, r26|->r25, r27|->r5, r27|->r6, r27|->r9, r27|->r12, r27|->r16, r27|->r17, r27|->r18, r27|->r20, r27|->r22, r27|->r24, r27|->r26, r28|->r2, r28|->r4, r28|->r5, r28|->r10, r28|->r12, r28|->r14, r28|->r16, r28|->r17, r28|->r19, r28|->r21, r28|->r22, r28|->r23, r28|->r25, r28|->r27, r29|->r2, r29|->r4, r29|->r6, r29|->r10, r29|->r12, r29|->r14, r29|->r17, r29|->r18, r29|->r19, r29|->r20, r29|->r21, r29|->r22, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s15,re:r25,mo:pro,pr: 4,co:{c15,c6,c0,c3,c1,c4,c9,c17,c11,c14,c12,c16})), rule1|->(rec(su:s2,re:r11,mo:pro,pr: 4,co:{c1,c18,c2,c12,c0,c6,c9,c19,c5,c11})), rule2|->(rec(su:s28,re:r25,mo:per,pr: 0,co:{c6,c9,c10,c2,c18,c12,c16,c1,c0,c17,c19,c14,c7,c15})), rule3|->(rec(su:s3,re:r11,mo:per,pr: 3,co:{c7,c15,c18,c4,c5,c16,c12})), rule4|->(rec(su:s0,re:r22,mo:pro,pr: 4,co:{c19,c5,c18,c1,c0,c14,c2,c7,c6})), rule5|->(rec(su:s21,re:r15,mo:per,pr: 4,co:{c11,c6,c9,c10,c12,c17,c13,c5,c8,c14})), rule6|->(rec(su:s5,re:r9,mo:per,pr: 3,co:{c0,c18,c4,c6,c17,c9})), rule7|->(rec(su:s20,re:r29,mo:per,pr: 0,co:{c16,c0,c11,c3,c17,c7,c19,c13,c4,c10,c14})), rule8|->(rec(su:s3,re:r13,mo:pro,pr: 2,co:{c0,c8,c6,c12,c9,c2,c16,c5,c7,c19,c10,c15})), rule9|->(rec(su:s12,re:r27,mo:per,pr: 0,co:{c14})), rule10|->(rec(su:s16,re:r2,mo:pro,pr: 3,co:{c2,c3,c16,c13,c17,c9,c0,c11,c19,c18,c14})), rule11|->(rec(su:s8,re:r2,mo:pro,pr: 1,co:{c7,c4,c6,c3,c12,c9,c17,c0,c18,c1}))}

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