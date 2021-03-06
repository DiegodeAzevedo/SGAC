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
    e_sub={s1|->s0, s3|->s1, s3|->s2, s5|->s2, s5|->s4, s6|->s1, s6|->s2, s6|->s4, s7|->s4, s7|->s6, s8|->s0, s8|->s3, s8|->s4, s8|->s6, s8|->s7, s9|->s0, s9|->s1, s9|->s4, s9|->s5, s9|->s8, s10|->s1, s10|->s3, s10|->s8, s10|->s9, s11|->s0, s11|->s2, s11|->s3, s11|->s4, s11|->s7, s11|->s8, s11|->s9, s12|->s2, s12|->s3, s12|->s6, s12|->s8, s12|->s9, s13|->s0, s13|->s1, s13|->s2, s13|->s7, s13|->s10, s14|->s0, s14|->s1, s14|->s2, s14|->s3, s14|->s4, s14|->s7, s14|->s13, s15|->s2, s15|->s4, s15|->s5, s15|->s7, s15|->s8, s15|->s9, s15|->s10, s15|->s12, s15|->s13, s15|->s14, s16|->s1, s16|->s4, s16|->s5, s16|->s7, s16|->s8, s16|->s12, s16|->s14, s17|->s0, s17|->s1, s17|->s2, s17|->s4, s17|->s6, s17|->s7, s17|->s9, s17|->s10, s17|->s11, s17|->s13, s17|->s14, s17|->s16, s18|->s0, s18|->s3, s18|->s5, s18|->s7, s18|->s10, s18|->s11, s18|->s12, s18|->s13, s18|->s14, s18|->s17, s19|->s2, s19|->s4, s19|->s5, s19|->s6, s19|->s8, s19|->s11, s19|->s12, s19|->s15, s20|->s1, s20|->s2, s20|->s4, s20|->s6, s20|->s7, s20|->s9, s20|->s10, s20|->s13, s20|->s15, s20|->s16, s20|->s17, s20|->s18, s20|->s19, s21|->s1, s21|->s2, s21|->s3, s21|->s4, s21|->s5, s21|->s7, s21|->s8, s21|->s16, s21|->s17, s21|->s18, s21|->s20, s22|->s0, s22|->s2, s22|->s5, s22|->s6, s22|->s7, s22|->s10, s22|->s11, s22|->s12, s22|->s16, s22|->s18, s23|->s1, s23|->s5, s23|->s7, s23|->s10, s23|->s11, s23|->s14, s23|->s15, s23|->s17, s23|->s18, s23|->s22, s24|->s0, s24|->s2, s24|->s4, s24|->s8, s24|->s10, s24|->s11, s24|->s13, s24|->s17, s24|->s18, s24|->s21, s24|->s23, s25|->s0, s25|->s4, s25|->s9, s25|->s10, s25|->s11, s25|->s13, s25|->s15, s25|->s16, s25|->s20, s25|->s22, s25|->s24, s26|->s0, s26|->s2, s26|->s3, s26|->s6, s26|->s7, s26|->s9, s26|->s11, s26|->s12, s26|->s13, s26|->s14, s26|->s16, s26|->s17, s26|->s18, s26|->s22, s26|->s23, s26|->s24, s27|->s1, s27|->s6, s27|->s7, s27|->s8, s27|->s18, s27|->s20, s27|->s21, s27|->s23, s27|->s24, s27|->s26, s28|->s2, s28|->s4, s28|->s8, s28|->s12, s28|->s13, s28|->s14, s28|->s19, s28|->s20, s28|->s23, s28|->s27, s29|->s0, s29|->s2, s29|->s4, s29|->s6, s29|->s7, s29|->s10, s29|->s13, s29|->s15, s29|->s18, s29|->s21, s29|->s23, s29|->s24, s29|->s27, s30|->s2, s30|->s8, s30|->s11, s30|->s12, s30|->s13, s30|->s15, s30|->s16, s30|->s17, s30|->s18, s30|->s20, s30|->s21, s30|->s26, s31|->s0, s31|->s2, s31|->s3, s31|->s5, s31|->s6, s31|->s7, s31|->s8, s31|->s9, s31|->s10, s31|->s11, s31|->s19, s31|->s21, s31|->s22, s31|->s24, s31|->s26, s31|->s27, s31|->s28, s31|->s29, s31|->s30, s32|->s0, s32|->s7, s32|->s8, s32|->s9, s32|->s10, s32|->s11, s32|->s12, s32|->s14, s32|->s17, s32|->s20, s32|->s23, s32|->s24, s32|->s29, s32|->s30, s32|->s31, s33|->s1, s33|->s3, s33|->s4, s33|->s5, s33|->s8, s33|->s9, s33|->s10, s33|->s13, s33|->s14, s33|->s16, s33|->s20, s33|->s22, s33|->s23, s33|->s27, s33|->s28, s33|->s29, s33|->s31, s33|->s32, s34|->s1, s34|->s7, s34|->s8, s34|->s9, s34|->s11, s34|->s12, s34|->s13, s34|->s21, s34|->s22, s34|->s23, s34|->s25, s34|->s29, s34|->s30, s34|->s32, s34|->s33, s35|->s1, s35|->s2, s35|->s4, s35|->s8, s35|->s10, s35|->s11, s35|->s12, s35|->s13, s35|->s14, s35|->s15, s35|->s16, s35|->s17, s35|->s19, s35|->s23, s35|->s25, s35|->s29, s35|->s30, s35|->s31, s36|->s0, s36|->s1, s36|->s2, s36|->s5, s36|->s6, s36|->s12, s36|->s13, s36|->s15, s36|->s17, s36|->s19, s36|->s20, s36|->s21, s36|->s26, s36|->s27, s36|->s29, s36|->s30, s36|->s31, s36|->s35, s37|->s2, s37|->s4, s37|->s5, s37|->s6, s37|->s8, s37|->s9, s37|->s10, s37|->s13, s37|->s15, s37|->s16, s37|->s17, s37|->s18, s37|->s20, s37|->s24, s37|->s26, s37|->s28, s37|->s29, s37|->s30, s37|->s32, s37|->s33, s37|->s34, s37|->s35, s38|->s0, s38|->s3, s38|->s4, s38|->s5, s38|->s7, s38|->s8, s38|->s9, s38|->s10, s38|->s13, s38|->s14, s38|->s16, s38|->s18, s38|->s19, s38|->s23, s38|->s24, s38|->s30, s38|->s32, s38|->s34, s38|->s35, s38|->s36, s39|->s0, s39|->s3, s39|->s5, s39|->s6, s39|->s8, s39|->s10, s39|->s12, s39|->s13, s39|->s17, s39|->s20, s39|->s23, s39|->s25, s39|->s26, s39|->s28, s39|->s30, s39|->s32, s39|->s33, s39|->s35} &
    e_res={r1|->r0, r2|->r1, r3|->r0, r3|->r1, r3|->r2, r4|->r2, r5|->r0, r5|->r1, r5|->r2, r5|->r3, r5|->r4, r6|->r0, r6|->r1, r6|->r2, r6|->r3, r7|->r0, r7|->r2, r7|->r5, r8|->r0, r8|->r2, r8|->r5, r9|->r1, r9|->r5, r9|->r6, r9|->r8, r10|->r3, r10|->r6, r10|->r7, r10|->r8, r11|->r1, r11|->r5, r11|->r6, r11|->r7, r11|->r8, r11|->r9, r11|->r10, r12|->r0, r12|->r1, r12|->r6, r12|->r11, r13|->r0, r13|->r1, r13|->r2, r13|->r4, r13|->r5, r13|->r9, r13|->r10, r13|->r11, r13|->r12, r14|->r1, r14|->r3, r14|->r5, r14|->r6, r14|->r8, r14|->r9, r14|->r13, r15|->r0, r15|->r1, r15|->r2, r15|->r3, r15|->r4, r15|->r7, r15|->r9, r15|->r10, r15|->r11, r15|->r13, r16|->r0, r16|->r1, r16|->r3, r16|->r10, r16|->r11, r16|->r12, r16|->r13, r17|->r0, r17|->r4, r17|->r6, r17|->r7, r17|->r8, r17|->r11, r17|->r12, r17|->r14, r17|->r15, r18|->r3, r18|->r5, r18|->r7, r18|->r8, r18|->r9, r18|->r12, r18|->r16, r19|->r0, r19|->r2, r19|->r5, r19|->r8, r19|->r10, r19|->r11, r19|->r13, r19|->r18, r20|->r2, r20|->r4, r20|->r5, r20|->r8, r20|->r9, r20|->r10, r20|->r12, r20|->r15, r20|->r16, r20|->r17, r21|->r0, r21|->r1, r21|->r2, r21|->r7, r21|->r8, r21|->r10, r21|->r13, r21|->r17, r22|->r0, r22|->r1, r22|->r2, r22|->r4, r22|->r6, r22|->r8, r22|->r9, r22|->r12, r22|->r13, r22|->r14, r22|->r17, r22|->r20, r23|->r0, r23|->r3, r23|->r5, r23|->r11, r23|->r13, r23|->r14, r23|->r18, r23|->r21, r24|->r0, r24|->r8, r24|->r9, r24|->r10, r24|->r11, r24|->r12, r24|->r13, r24|->r15, r24|->r16, r24|->r20, r24|->r21, r24|->r23, r25|->r0, r25|->r1, r25|->r3, r25|->r5, r25|->r9, r25|->r12, r25|->r15, r25|->r19, r25|->r21, r25|->r24, r26|->r1, r26|->r4, r26|->r8, r26|->r9, r26|->r11, r26|->r13, r26|->r14, r26|->r15, r26|->r16, r26|->r18, r26|->r19, r26|->r21, r26|->r24, r26|->r25, r27|->r0, r27|->r1, r27|->r2, r27|->r5, r27|->r6, r27|->r7, r27|->r9, r27|->r12, r27|->r14, r27|->r15, r27|->r17, r27|->r18, r27|->r19, r27|->r23, r27|->r24, r27|->r25, r27|->r26, r28|->r0, r28|->r1, r28|->r4, r28|->r6, r28|->r7, r28|->r8, r28|->r11, r28|->r13, r28|->r15, r28|->r17, r28|->r20, r28|->r22, r28|->r26, r28|->r27, r29|->r1, r29|->r2, r29|->r4, r29|->r5, r29|->r8, r29|->r10, r29|->r13, r29|->r14, r29|->r18, r29|->r19, r29|->r22, r29|->r23, r29|->r25, r29|->r27, r30|->r0, r30|->r1, r30|->r2, r30|->r3, r30|->r4, r30|->r8, r30|->r9, r30|->r12, r30|->r13, r30|->r17, r30|->r18, r30|->r23, r30|->r24, r30|->r25, r30|->r26, r30|->r27, r30|->r28, r30|->r29, r31|->r5, r31|->r6, r31|->r11, r31|->r15, r31|->r16, r31|->r19, r31|->r20, r31|->r24, r31|->r27, r31|->r28, r31|->r30, r32|->r1, r32|->r3, r32|->r6, r32|->r7, r32|->r8, r32|->r10, r32|->r11, r32|->r14, r32|->r15, r32|->r16, r32|->r18, r32|->r20, r32|->r23, r32|->r25, r32|->r26, r32|->r28, r33|->r1, r33|->r2, r33|->r9, r33|->r10, r33|->r11, r33|->r12, r33|->r13, r33|->r17, r33|->r21, r33|->r22, r33|->r25, r33|->r26, r33|->r28, r33|->r30, r33|->r31, r34|->r0, r34|->r1, r34|->r5, r34|->r6, r34|->r16, r34|->r19, r34|->r22, r34|->r25, r34|->r27, r34|->r29, r34|->r30, r34|->r32, r34|->r33, r35|->r9, r35|->r10, r35|->r13, r35|->r14, r35|->r16, r35|->r17, r35|->r18, r35|->r20, r35|->r22, r35|->r23, r35|->r25, r35|->r29, r35|->r31, r35|->r32, r35|->r33, r36|->r0, r36|->r1, r36|->r2, r36|->r5, r36|->r7, r36|->r8, r36|->r10, r36|->r11, r36|->r12, r36|->r14, r36|->r16, r36|->r17, r36|->r18, r36|->r20, r36|->r21, r36|->r22, r36|->r23, r36|->r24, r36|->r25, r36|->r28, r36|->r32, r36|->r34, r36|->r35, r37|->r0, r37|->r2, r37|->r4, r37|->r5, r37|->r6, r37|->r12, r37|->r14, r37|->r15, r37|->r17, r37|->r18, r37|->r19, r37|->r20, r37|->r21, r37|->r22, r37|->r23, r37|->r24, r37|->r26, r37|->r28, r37|->r29, r37|->r31, r37|->r33, r37|->r34, r37|->r36, r38|->r1, r38|->r3, r38|->r7, r38|->r8, r38|->r9, r38|->r12, r38|->r13, r38|->r15, r38|->r18, r38|->r20, r38|->r21, r38|->r23, r38|->r25, r38|->r28, r38|->r31, r38|->r32, r38|->r34, r38|->r35, r38|->r37, r39|->r2, r39|->r6, r39|->r7, r39|->r8, r39|->r9, r39|->r11, r39|->r16, r39|->r17, r39|->r22, r39|->r26, r39|->r30, r39|->r31, r39|->r32, r39|->r34, r39|->r35} &
    rules={rule0|->(rec(su:s27,re:r9,mo:pro,pr: 0,co:{c0})), rule1|->(rec(su:s37,re:r28,mo:per,pr: 4,co:{c8,c6,c0,c4})), rule2|->(rec(su:s29,re:r24,mo:per,pr: 1,co:{c0,c7,c3})), rule3|->(rec(su:s26,re:r10,mo:per,pr: 4,co:{c6,c3,c1})), rule4|->(rec(su:s1,re:r24,mo:pro,pr: 2,co:{c9,c7,c3,c8})), rule5|->(rec(su:s17,re:r18,mo:per,pr: 1,co:{c8,c5,c2,c9,c4,c3})), rule6|->(rec(su:s24,re:r14,mo:pro,pr: 4,co:{c7,c1,c3})), rule7|->(rec(su:s35,re:r18,mo:pro,pr: 2,co:{c7,c4,c2})), rule8|->(rec(su:s21,re:r26,mo:per,pr: 1,co:{c9,c5,c4,c8})), rule9|->(rec(su:s37,re:r13,mo:pro,pr: 2,co:{c5,c0,c9,c3})), rule10|->(rec(su:s27,re:r1,mo:pro,pr: 3,co:{c2,c0,c1})), rule11|->(rec(su:s34,re:r31,mo:pro,pr: 0,co:{c7,c8,c9,c6,c0,c3})), rule12|->(rec(su:s14,re:r24,mo:per,pr: 3,co:{c4,c5}))}

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