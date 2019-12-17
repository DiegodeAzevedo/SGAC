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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36};
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
    e_sub={s1|->s0, s3|->s0, s3|->s1, s4|->s2, s4|->s3, s5|->s0, s5|->s1, s5|->s3, s5|->s4, s6|->s0, s6|->s1, s6|->s2, s6|->s5, s7|->s3, s7|->s4, s8|->s2, s8|->s3, s8|->s6, s8|->s7, s9|->s0, s9|->s2, s9|->s3, s9|->s4, s9|->s5, s9|->s6, s9|->s7, s9|->s8, s10|->s2, s10|->s3, s10|->s6, s11|->s0, s11|->s3, s11|->s4, s11|->s7, s11|->s8, s12|->s0, s12|->s4, s12|->s11, s13|->s0, s13|->s1, s13|->s2, s13|->s3, s13|->s7, s13|->s9, s13|->s10, s13|->s12, s14|->s0, s14|->s2, s14|->s3, s14|->s5, s14|->s6, s14|->s7, s14|->s11, s14|->s13, s15|->s0, s15|->s1, s15|->s2, s15|->s3, s15|->s5, s15|->s6, s15|->s8, s16|->s1, s16|->s2, s16|->s3, s16|->s6, s16|->s9, s17|->s0, s17|->s1, s17|->s3, s17|->s5, s17|->s8, s17|->s9, s17|->s10, s17|->s11, s17|->s13, s17|->s15, s17|->s16, s18|->s0, s18|->s2, s18|->s3, s18|->s5, s18|->s7, s18|->s9, s18|->s15, s19|->s2, s19|->s3, s19|->s4, s19|->s8, s19|->s10, s19|->s12, s19|->s13, s20|->s1, s20|->s2, s20|->s4, s20|->s9, s20|->s11, s20|->s14, s20|->s15, s20|->s18, s20|->s19, s21|->s0, s21|->s2, s21|->s3, s21|->s4, s21|->s5, s21|->s7, s21|->s9, s21|->s10, s21|->s12, s21|->s13, s21|->s15, s21|->s16, s21|->s17, s21|->s18, s22|->s0, s22|->s3, s22|->s4, s22|->s5, s22|->s7, s22|->s8, s22|->s10, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s18, s22|->s19, s23|->s0, s23|->s2, s23|->s3, s23|->s7, s23|->s10, s23|->s11, s23|->s13, s23|->s15, s23|->s18, s23|->s19, s24|->s1, s24|->s2, s24|->s3, s24|->s5, s24|->s7, s24|->s9, s24|->s10, s24|->s11, s24|->s14, s24|->s18, s24|->s23, s25|->s1, s25|->s3, s25|->s5, s25|->s6, s25|->s10, s25|->s12, s25|->s13, s25|->s15, s25|->s17, s25|->s18, s25|->s19, s25|->s20, s26|->s0, s26|->s3, s26|->s5, s26|->s8, s26|->s9, s26|->s14, s26|->s15, s26|->s16, s26|->s17, s26|->s18, s26|->s20, s26|->s21, s26|->s25, s27|->s4, s27|->s6, s27|->s8, s27|->s9, s27|->s10, s27|->s14, s27|->s16, s27|->s17, s27|->s19, s27|->s20, s27|->s21, s27|->s23, s27|->s25, s27|->s26, s28|->s3, s28|->s5, s28|->s7, s28|->s8, s28|->s9, s28|->s11, s28|->s13, s28|->s15, s28|->s18, s28|->s19, s28|->s20, s28|->s21, s28|->s24, s28|->s27, s29|->s0, s29|->s1, s29|->s2, s29|->s5, s29|->s6, s29|->s9, s29|->s11, s29|->s14, s29|->s15, s29|->s18, s29|->s21, s29|->s22, s29|->s23, s29|->s24, s29|->s25, s29|->s26, s29|->s27, s29|->s28, s30|->s5, s30|->s6, s30|->s7, s30|->s8, s30|->s9, s30|->s11, s30|->s12, s30|->s14, s30|->s15, s30|->s16, s30|->s17, s30|->s19, s30|->s21, s30|->s26, s30|->s27, s30|->s28, s30|->s29, s31|->s1, s31|->s2, s31|->s3, s31|->s4, s31|->s6, s31|->s8, s31|->s9, s31|->s11, s31|->s12, s31|->s15, s31|->s17, s31|->s19, s31|->s21, s31|->s23, s31|->s25, s31|->s26, s31|->s27, s31|->s28, s31|->s29, s32|->s0, s32|->s2, s32|->s5, s32|->s6, s32|->s10, s32|->s13, s32|->s15, s32|->s16, s32|->s17, s32|->s19, s32|->s21, s32|->s23, s32|->s24, s32|->s25, s32|->s26, s32|->s27, s32|->s28, s32|->s30, s33|->s0, s33|->s3, s33|->s4, s33|->s5, s33|->s6, s33|->s11, s33|->s12, s33|->s14, s33|->s16, s33|->s17, s33|->s20, s33|->s23, s33|->s24, s33|->s25, s33|->s28, s33|->s30, s33|->s31, s34|->s2, s34|->s3, s34|->s6, s34|->s9, s34|->s12, s34|->s13, s34|->s14, s34|->s15, s34|->s18, s34|->s20, s34|->s22, s34|->s23, s34|->s24, s34|->s27, s34|->s28, s34|->s31, s34|->s33, s35|->s0, s35|->s1, s35|->s2, s35|->s6, s35|->s9, s35|->s13, s35|->s14, s35|->s15, s35|->s16, s35|->s17, s35|->s19, s35|->s24, s35|->s25, s35|->s27, s35|->s28, s35|->s29, s35|->s30, s35|->s33, s36|->s0, s36|->s1, s36|->s2, s36|->s4, s36|->s12, s36|->s13, s36|->s14, s36|->s15, s36|->s17, s36|->s18, s36|->s19, s36|->s21, s36|->s23, s36|->s24, s36|->s25, s36|->s29, s36|->s31, s36|->s33, s36|->s34, s36|->s35, s37|->s0, s37|->s3, s37|->s5, s37|->s6, s37|->s8, s37|->s9, s37|->s10, s37|->s13, s37|->s14, s37|->s15, s37|->s16, s37|->s20, s37|->s21, s37|->s23, s37|->s25, s37|->s27, s37|->s28, s37|->s29, s37|->s30, s37|->s32, s37|->s33, s37|->s34} &
    e_res={r2|->r0, r3|->r0, r4|->r1, r4|->r2, r5|->r1, r5|->r2, r6|->r1, r6|->r2, r6|->r3, r7|->r2, r7|->r6, r8|->r0, r8|->r3, r8|->r4, r8|->r6, r8|->r7, r9|->r0, r9|->r1, r9|->r2, r9|->r4, r9|->r8, r10|->r0, r10|->r2, r10|->r5, r10|->r7, r10|->r8, r11|->r0, r11|->r1, r11|->r2, r11|->r3, r11|->r4, r11|->r7, r11|->r8, r11|->r9, r12|->r2, r12|->r4, r12|->r7, r12|->r8, r12|->r9, r12|->r11, r13|->r0, r13|->r2, r13|->r4, r13|->r5, r13|->r7, r13|->r9, r13|->r11, r13|->r12, r14|->r0, r14|->r2, r14|->r3, r14|->r4, r14|->r6, r14|->r8, r14|->r10, r14|->r11, r14|->r12, r14|->r13, r15|->r3, r15|->r6, r15|->r8, r15|->r9, r15|->r13, r15|->r14, r16|->r0, r16|->r1, r16|->r2, r16|->r4, r16|->r5, r16|->r6, r16|->r7, r16|->r9, r16|->r14, r16|->r15, r17|->r1, r17|->r2, r17|->r7, r17|->r8, r17|->r9, r17|->r10, r17|->r12, r17|->r13, r17|->r14, r17|->r15, r17|->r16, r18|->r1, r18|->r4, r18|->r5, r18|->r10, r18|->r14, r18|->r15, r18|->r17, r19|->r0, r19|->r1, r19|->r3, r19|->r7, r19|->r8, r19|->r11, r19|->r13, r19|->r14, r19|->r15, r19|->r17, r19|->r18, r20|->r2, r20|->r4, r20|->r8, r20|->r14, r20|->r15, r20|->r18, r21|->r5, r21|->r7, r21|->r8, r21|->r10, r21|->r12, r21|->r16, r21|->r19, r22|->r1, r22|->r2, r22|->r3, r22|->r4, r22|->r7, r22|->r9, r22|->r11, r22|->r13, r22|->r14, r22|->r19, r23|->r7, r23|->r9, r23|->r11, r23|->r12, r23|->r19, r24|->r1, r24|->r3, r24|->r4, r24|->r6, r24|->r11, r24|->r12, r24|->r17, r24|->r19, r24|->r20, r24|->r21, r25|->r0, r25|->r3, r25|->r4, r25|->r6, r25|->r8, r25|->r10, r25|->r12, r25|->r13, r25|->r14, r25|->r16, r25|->r18, r25|->r19, r25|->r24, r26|->r1, r26|->r2, r26|->r3, r26|->r5, r26|->r11, r26|->r12, r26|->r16, r26|->r17, r26|->r18, r26|->r23, r26|->r25, r27|->r0, r27|->r2, r27|->r4, r27|->r8, r27|->r9, r27|->r12, r27|->r13, r27|->r15, r27|->r16, r27|->r17, r27|->r18, r27|->r20, r27|->r21, r27|->r24, r28|->r0, r28|->r1, r28|->r2, r28|->r5, r28|->r6, r28|->r12, r28|->r13, r28|->r17, r28|->r19, r28|->r20, r28|->r22, r28|->r23, r28|->r26, r28|->r27, r29|->r3, r29|->r5, r29|->r6, r29|->r7, r29|->r11, r29|->r12, r29|->r15, r29|->r17, r29|->r19, r29|->r21, r29|->r22, r29|->r28, r30|->r1, r30|->r2, r30|->r8, r30|->r10, r30|->r12, r30|->r13, r30|->r16, r30|->r17, r30|->r18, r30|->r19, r30|->r20, r30|->r22, r30|->r23, r30|->r27, r30|->r28, r31|->r0, r31|->r3, r31|->r4, r31|->r5, r31|->r7, r31|->r8, r31|->r10, r31|->r12, r31|->r14, r31|->r16, r31|->r18, r31|->r19, r31|->r20, r31|->r21, r31|->r22, r31|->r23, r31|->r26, r31|->r29, r32|->r3, r32|->r4, r32|->r5, r32|->r6, r32|->r7, r32|->r8, r32|->r9, r32|->r10, r32|->r16, r32|->r19, r32|->r22, r32|->r23, r32|->r25, r32|->r26, r32|->r27, r32|->r29, r32|->r30, r32|->r31, r33|->r3, r33|->r5, r33|->r11, r33|->r13, r33|->r15, r33|->r19, r33|->r21, r33|->r26, r33|->r29, r33|->r32, r34|->r0, r34|->r2, r34|->r4, r34|->r6, r34|->r8, r34|->r9, r34|->r11, r34|->r15, r34|->r20, r34|->r23, r34|->r24, r34|->r25, r34|->r26, r34|->r27, r34|->r28, r34|->r31, r34|->r32, r34|->r33, r35|->r1, r35|->r2, r35|->r5, r35|->r6, r35|->r7, r35|->r8, r35|->r10, r35|->r11, r35|->r12, r35|->r13, r35|->r14, r35|->r16, r35|->r17, r35|->r21, r35|->r24, r35|->r25, r35|->r29, r35|->r30, r35|->r31, r35|->r32, r35|->r33, r35|->r34, r36|->r1, r36|->r3, r36|->r6, r36|->r7, r36|->r8, r36|->r13, r36|->r16, r36|->r18, r36|->r22, r36|->r25, r36|->r27, r36|->r28, r36|->r29, r36|->r31, r36|->r34, r36|->r35} &
    rules={rule0|->(rec(su:s30,re:r19,mo:pro,pr: 2,co:{c5,c6,c9,c7,c2})), rule1|->(rec(su:s8,re:r35,mo:per,pr: 1,co:{c5,c6,c7,c8,c2})), rule2|->(rec(su:s1,re:r6,mo:pro,pr: 1,co:{c6,c5,c4,c9})), rule3|->(rec(su:s18,re:r4,mo:pro,pr: 3,co:{c1,c2,c6,c0,c9})), rule4|->(rec(su:s18,re:r19,mo:pro,pr: 4,co:{c1,c7,c9})), rule5|->(rec(su:s22,re:r35,mo:per,pr: 1,co:{c8,c9,c0,c5,c2,c4,c6,c7,c3})), rule6|->(rec(su:s18,re:r2,mo:per,pr: 0,co:{c6,c9,c0,c4,c8,c7})), rule7|->(rec(su:s25,re:r1,mo:pro,pr: 1,co:{c0,c9,c5,c1,c7})), rule8|->(rec(su:s15,re:r28,mo:per,pr: 1,co:{c3,c1,c4,c6})), rule9|->(rec(su:s15,re:r11,mo:per,pr: 4,co:{c7,c6,c9,c1,c3})), rule10|->(rec(su:s16,re:r36,mo:pro,pr: 2,co:{c7,c4,c1,c2,c3})), rule11|->(rec(su:s20,re:r16,mo:per,pr: 4,co:{c9,c5})), rule12|->(rec(su:s23,re:r31,mo:per,pr: 1,co:{c4,c6,c9}))}

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