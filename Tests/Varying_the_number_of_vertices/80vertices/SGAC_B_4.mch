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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39};
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
    e_sub={s1|->s0, s2|->s0, s3|->s0, s3|->s1, s3|->s2, s4|->s0, s4|->s2, s5|->s0, s5|->s1, s5|->s2, s6|->s0, s6|->s1, s6|->s2, s6|->s3, s7|->s1, s7|->s2, s7|->s5, s7|->s6, s8|->s3, s8|->s4, s8|->s5, s8|->s7, s9|->s1, s9|->s4, s9|->s5, s9|->s8, s10|->s6, s10|->s9, s11|->s0, s11|->s1, s11|->s3, s11|->s4, s11|->s5, s11|->s7, s11|->s10, s12|->s1, s12|->s3, s12|->s4, s12|->s6, s12|->s9, s12|->s10, s13|->s0, s13|->s5, s13|->s6, s13|->s9, s13|->s12, s14|->s0, s14|->s1, s14|->s4, s14|->s6, s14|->s9, s14|->s12, s15|->s0, s15|->s1, s15|->s3, s15|->s6, s15|->s7, s15|->s8, s15|->s9, s15|->s12, s15|->s13, s16|->s1, s16|->s2, s16|->s4, s16|->s7, s16|->s12, s16|->s15, s17|->s4, s17|->s5, s17|->s8, s17|->s9, s17|->s11, s17|->s12, s17|->s15, s18|->s0, s18|->s4, s18|->s5, s18|->s7, s18|->s9, s18|->s10, s18|->s14, s18|->s15, s18|->s17, s19|->s1, s19|->s3, s19|->s5, s19|->s6, s19|->s8, s19|->s9, s19|->s12, s19|->s13, s19|->s14, s19|->s15, s19|->s16, s19|->s17, s20|->s1, s20|->s2, s20|->s3, s20|->s6, s20|->s7, s20|->s10, s20|->s11, s20|->s16, s20|->s19, s21|->s1, s21|->s2, s21|->s4, s21|->s5, s21|->s7, s21|->s9, s21|->s18, s22|->s1, s22|->s2, s22|->s3, s22|->s6, s22|->s7, s22|->s16, s22|->s19, s23|->s5, s23|->s9, s23|->s10, s23|->s12, s23|->s13, s23|->s15, s23|->s16, s23|->s17, s23|->s22, s24|->s2, s24|->s3, s24|->s4, s24|->s7, s24|->s10, s24|->s13, s24|->s14, s24|->s15, s24|->s17, s24|->s23, s25|->s0, s25|->s3, s25|->s4, s25|->s5, s25|->s7, s25|->s9, s25|->s11, s25|->s12, s25|->s13, s25|->s14, s25|->s21, s25|->s23, s25|->s24, s26|->s1, s26|->s2, s26|->s3, s26|->s5, s26|->s7, s26|->s8, s26|->s10, s26|->s11, s26|->s14, s26|->s16, s26|->s17, s26|->s23, s26|->s24, s27|->s3, s27|->s7, s27|->s8, s27|->s11, s27|->s13, s27|->s14, s27|->s15, s27|->s17, s27|->s18, s27|->s22, s27|->s24, s28|->s2, s28|->s5, s28|->s6, s28|->s10, s28|->s11, s28|->s15, s28|->s16, s28|->s19, s28|->s20, s28|->s25, s28|->s27, s29|->s1, s29|->s5, s29|->s9, s29|->s14, s29|->s16, s29|->s17, s29|->s18, s29|->s20, s29|->s21, s29|->s22, s29|->s23, s29|->s24, s29|->s26, s29|->s27, s29|->s28, s30|->s0, s30|->s1, s30|->s6, s30|->s8, s30|->s9, s30|->s11, s30|->s14, s30|->s15, s30|->s17, s30|->s18, s30|->s21, s30|->s22, s30|->s24, s30|->s26, s30|->s27, s30|->s28, s31|->s2, s31|->s4, s31|->s6, s31|->s7, s31|->s9, s31|->s10, s31|->s11, s31|->s14, s31|->s15, s31|->s16, s31|->s18, s31|->s19, s31|->s20, s31|->s21, s31|->s25, s31|->s26, s31|->s27, s31|->s29, s32|->s0, s32|->s1, s32|->s2, s32|->s3, s32|->s7, s32|->s12, s32|->s13, s32|->s14, s32|->s18, s32|->s19, s32|->s22, s32|->s24, s32|->s27, s33|->s3, s33|->s8, s33|->s12, s33|->s13, s33|->s20, s33|->s21, s33|->s26, s33|->s28, s33|->s30, s33|->s32, s34|->s0, s34|->s1, s34|->s6, s34|->s7, s34|->s10, s34|->s11, s34|->s15, s34|->s18, s34|->s19, s34|->s21, s34|->s24, s34|->s27, s34|->s28, s34|->s30, s34|->s33, s35|->s1, s35|->s2, s35|->s3, s35|->s4, s35|->s5, s35|->s7, s35|->s9, s35|->s14, s35|->s18, s35|->s19, s35|->s20, s35|->s21, s35|->s23, s35|->s24, s35|->s25, s35|->s26, s35|->s28, s35|->s30, s35|->s31, s35|->s32, s35|->s33, s35|->s34, s36|->s0, s36|->s1, s36|->s2, s36|->s6, s36|->s8, s36|->s9, s36|->s11, s36|->s13, s36|->s16, s36|->s17, s36|->s20, s36|->s22, s36|->s25, s36|->s27, s36|->s28, s36|->s32, s36|->s33, s36|->s34, s37|->s0, s37|->s2, s37|->s4, s37|->s5, s37|->s7, s37|->s9, s37|->s11, s37|->s15, s37|->s17, s37|->s20, s37|->s22, s37|->s26, s37|->s27, s37|->s28, s37|->s29, s37|->s30, s37|->s31, s37|->s32, s37|->s33, s38|->s1, s38|->s2, s38|->s7, s38|->s9, s38|->s10, s38|->s12, s38|->s15, s38|->s16, s38|->s17, s38|->s20, s38|->s21, s38|->s22, s38|->s25, s38|->s28, s38|->s30, s38|->s34, s38|->s36, s39|->s1, s39|->s3, s39|->s5, s39|->s6, s39|->s8, s39|->s9, s39|->s13, s39|->s17, s39|->s18, s39|->s20, s39|->s21, s39|->s22, s39|->s25, s39|->s26, s39|->s27, s39|->s28, s39|->s29, s39|->s32, s39|->s33, s39|->s34, s39|->s35, s39|->s36} &
    e_res={r2|->r0, r3|->r0, r3|->r1, r3|->r2, r4|->r0, r4|->r1, r4|->r2, r5|->r1, r5|->r2, r6|->r1, r6|->r2, r6|->r3, r7|->r0, r7|->r1, r7|->r2, r7|->r4, r8|->r0, r8|->r1, r8|->r4, r9|->r0, r9|->r4, r9|->r7, r9|->r8, r10|->r0, r10|->r2, r10|->r3, r10|->r4, r10|->r6, r10|->r7, r10|->r9, r11|->r0, r11|->r2, r11|->r4, r11|->r7, r12|->r2, r12|->r4, r12|->r5, r12|->r7, r12|->r8, r12|->r10, r13|->r0, r13|->r1, r13|->r2, r13|->r5, r13|->r7, r14|->r0, r14|->r3, r14|->r4, r14|->r6, r14|->r7, r14|->r8, r14|->r12, r15|->r0, r15|->r1, r15|->r3, r15|->r7, r15|->r9, r15|->r10, r15|->r11, r15|->r13, r16|->r0, r16|->r1, r16|->r2, r16|->r3, r16|->r5, r16|->r7, r16|->r11, r16|->r13, r16|->r15, r17|->r1, r17|->r3, r17|->r4, r17|->r5, r17|->r6, r17|->r7, r17|->r12, r18|->r2, r18|->r6, r18|->r7, r18|->r9, r18|->r12, r18|->r13, r18|->r15, r18|->r16, r18|->r17, r19|->r0, r19|->r1, r19|->r2, r19|->r3, r19|->r4, r19|->r5, r19|->r7, r19|->r8, r19|->r11, r19|->r12, r19|->r13, r19|->r15, r19|->r16, r20|->r1, r20|->r3, r20|->r4, r20|->r5, r20|->r6, r20|->r8, r20|->r10, r20|->r11, r20|->r12, r20|->r13, r20|->r15, r20|->r17, r21|->r1, r21|->r2, r21|->r4, r21|->r6, r21|->r9, r21|->r11, r21|->r13, r21|->r15, r21|->r20, r22|->r1, r22|->r2, r22|->r3, r22|->r7, r22|->r10, r22|->r12, r22|->r13, r22|->r15, r22|->r16, r22|->r19, r22|->r20, r23|->r0, r23|->r3, r23|->r5, r23|->r10, r23|->r11, r23|->r14, r23|->r15, r23|->r17, r23|->r18, r23|->r20, r23|->r22, r24|->r2, r24|->r4, r24|->r6, r24|->r11, r24|->r12, r24|->r14, r24|->r15, r24|->r16, r24|->r18, r24|->r19, r24|->r21, r24|->r23, r25|->r0, r25|->r3, r25|->r5, r25|->r6, r25|->r7, r25|->r9, r25|->r11, r25|->r12, r25|->r13, r25|->r14, r25|->r17, r25|->r18, r25|->r22, r25|->r24, r26|->r3, r26|->r5, r26|->r6, r26|->r14, r26|->r15, r26|->r17, r26|->r19, r26|->r20, r26|->r21, r26|->r22, r26|->r23, r26|->r25, r27|->r0, r27|->r1, r27|->r2, r27|->r3, r27|->r4, r27|->r5, r27|->r6, r27|->r7, r27|->r8, r27|->r10, r27|->r13, r27|->r15, r27|->r16, r27|->r18, r27|->r19, r27|->r21, r27|->r23, r27|->r26, r28|->r3, r28|->r4, r28|->r5, r28|->r6, r28|->r7, r28|->r9, r28|->r11, r28|->r12, r28|->r14, r28|->r17, r28|->r23, r28|->r25, r29|->r0, r29|->r1, r29|->r2, r29|->r3, r29|->r6, r29|->r8, r29|->r10, r29|->r11, r29|->r12, r29|->r15, r29|->r20, r29|->r23, r29|->r26, r30|->r0, r30|->r1, r30|->r3, r30|->r9, r30|->r10, r30|->r12, r30|->r13, r30|->r15, r30|->r16, r30|->r18, r30|->r21, r30|->r22, r30|->r26, r30|->r29, r31|->r1, r31|->r2, r31|->r7, r31|->r8, r31|->r11, r31|->r12, r31|->r15, r31|->r19, r31|->r20, r31|->r21, r31|->r24, r31|->r26, r31|->r28, r31|->r30, r32|->r0, r32|->r2, r32|->r5, r32|->r6, r32|->r7, r32|->r9, r32|->r10, r32|->r11, r32|->r12, r32|->r15, r32|->r16, r32|->r19, r32|->r20, r32|->r21, r32|->r22, r32|->r26, r32|->r28, r33|->r5, r33|->r6, r33|->r7, r33|->r8, r33|->r9, r33|->r10, r33|->r12, r33|->r15, r33|->r17, r33|->r19, r33|->r22, r33|->r24, r33|->r25, r33|->r28, r33|->r29, r33|->r30, r34|->r0, r34|->r2, r34|->r3, r34|->r4, r34|->r7, r34|->r9, r34|->r15, r34|->r18, r34|->r19, r34|->r21, r34|->r22, r34|->r26, r34|->r28, r34|->r29, r34|->r31, r35|->r0, r35|->r1, r35|->r3, r35|->r4, r35|->r6, r35|->r8, r35|->r9, r35|->r13, r35|->r14, r35|->r15, r35|->r16, r35|->r17, r35|->r21, r35|->r23, r35|->r24, r35|->r26, r35|->r29, r35|->r32, r35|->r33, r35|->r34, r36|->r1, r36|->r4, r36|->r5, r36|->r6, r36|->r9, r36|->r11, r36|->r13, r36|->r14, r36|->r19, r36|->r20, r36|->r21, r36|->r22, r36|->r23, r36|->r24, r36|->r25, r36|->r27, r36|->r29, r36|->r30, r36|->r33, r37|->r1, r37|->r2, r37|->r5, r37|->r6, r37|->r8, r37|->r10, r37|->r11, r37|->r13, r37|->r16, r37|->r20, r37|->r21, r37|->r22, r37|->r25, r37|->r28, r37|->r30, r37|->r31, r37|->r33, r37|->r34, r38|->r1, r38|->r4, r38|->r6, r38|->r8, r38|->r9, r38|->r10, r38|->r12, r38|->r15, r38|->r16, r38|->r17, r38|->r18, r38|->r19, r38|->r22, r38|->r24, r38|->r29, r38|->r33, r38|->r34, r38|->r35, r38|->r36, r38|->r37, r39|->r0, r39|->r2, r39|->r3, r39|->r4, r39|->r5, r39|->r8, r39|->r10, r39|->r11, r39|->r13, r39|->r17, r39|->r22, r39|->r23, r39|->r24, r39|->r28, r39|->r34, r39|->r35, r39|->r36, r39|->r38} &
    rules={rule0|->(rec(su:s34,re:r19,mo:pro,pr: 2,co:{c7})), rule1|->(rec(su:s15,re:r39,mo:pro,pr: 3,co:{c7,c8,c2,c3,c1})), rule2|->(rec(su:s38,re:r36,mo:pro,pr: 3,co:{c3,c5,c9,c1})), rule3|->(rec(su:s26,re:r22,mo:pro,pr: 4,co:{c3,c5,c7,c9,c6,c8})), rule4|->(rec(su:s28,re:r22,mo:per,pr: 4,co:{c7,c1,c6,c3})), rule5|->(rec(su:s6,re:r23,mo:pro,pr: 4,co:{c5,c7})), rule6|->(rec(su:s35,re:r9,mo:pro,pr: 3,co:{c1,c2,c6,c5,c9,c8,c3})), rule7|->(rec(su:s16,re:r21,mo:per,pr: 0,co:{c9,c8,c4,c7,c1,c5})), rule8|->(rec(su:s17,re:r22,mo:per,pr: 2,co:{c2,c0,c1,c7,c4,c3,c9})), rule9|->(rec(su:s39,re:r1,mo:per,pr: 1,co:{c1,c6,c4})), rule10|->(rec(su:s10,re:r10,mo:per,pr: 4,co:{c2,c5,c8})), rule11|->(rec(su:s35,re:r14,mo:pro,pr: 4,co:{c8,c9,c0,c3,c1})), rule12|->(rec(su:s34,re:r31,mo:per,pr: 3,co:{c7,c0,c9,c5}))}

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