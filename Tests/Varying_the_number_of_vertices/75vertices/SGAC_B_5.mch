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
    e_sub={s2|->s0, s3|->s2, s4|->s0, s4|->s1, s4|->s3, s5|->s3, s5|->s4, s6|->s1, s6|->s2, s6|->s4, s6|->s5, s7|->s1, s7|->s2, s7|->s3, s7|->s5, s7|->s6, s8|->s1, s8|->s2, s8|->s3, s8|->s7, s9|->s2, s9|->s3, s9|->s5, s9|->s7, s10|->s0, s10|->s1, s10|->s4, s10|->s5, s10|->s6, s10|->s9, s11|->s0, s11|->s2, s11|->s3, s11|->s7, s12|->s0, s12|->s2, s12|->s3, s12|->s4, s12|->s5, s12|->s6, s13|->s0, s13|->s3, s13|->s6, s13|->s8, s13|->s9, s13|->s12, s14|->s2, s14|->s4, s14|->s5, s14|->s6, s14|->s8, s14|->s9, s15|->s0, s15|->s2, s15|->s5, s15|->s7, s15|->s8, s15|->s11, s15|->s12, s15|->s13, s15|->s14, s16|->s0, s16|->s4, s16|->s5, s16|->s6, s16|->s7, s16|->s8, s16|->s14, s17|->s2, s17|->s3, s17|->s4, s17|->s5, s17|->s9, s17|->s10, s17|->s12, s18|->s0, s18|->s1, s18|->s3, s18|->s5, s18|->s6, s18|->s8, s18|->s13, s18|->s16, s19|->s0, s19|->s5, s19|->s6, s19|->s7, s19|->s10, s19|->s11, s20|->s0, s20|->s6, s20|->s9, s20|->s10, s20|->s13, s20|->s19, s21|->s0, s21|->s2, s21|->s4, s21|->s5, s21|->s6, s21|->s8, s21|->s12, s21|->s14, s21|->s15, s21|->s16, s21|->s17, s21|->s18, s21|->s19, s22|->s0, s22|->s2, s22|->s4, s22|->s6, s22|->s8, s22|->s9, s22|->s10, s22|->s13, s22|->s17, s22|->s21, s23|->s2, s23|->s3, s23|->s4, s23|->s6, s23|->s9, s23|->s10, s23|->s11, s23|->s12, s23|->s16, s23|->s18, s23|->s19, s23|->s20, s23|->s21, s24|->s0, s24|->s1, s24|->s2, s24|->s4, s24|->s6, s24|->s8, s24|->s9, s24|->s11, s24|->s13, s24|->s14, s24|->s20, s24|->s23, s25|->s0, s25|->s4, s25|->s5, s25|->s9, s25|->s12, s25|->s14, s25|->s15, s25|->s16, s25|->s17, s25|->s19, s25|->s22, s25|->s23, s25|->s24, s26|->s1, s26|->s2, s26|->s4, s26|->s6, s26|->s7, s26|->s8, s26|->s10, s26|->s11, s26|->s13, s26|->s15, s26|->s16, s26|->s19, s26|->s22, s26|->s24, s26|->s25, s27|->s0, s27|->s3, s27|->s4, s27|->s5, s27|->s6, s27|->s7, s27|->s8, s27|->s10, s27|->s11, s27|->s13, s27|->s20, s27|->s22, s27|->s25, s27|->s26, s28|->s0, s28|->s5, s28|->s9, s28|->s10, s28|->s13, s28|->s18, s28|->s19, s28|->s20, s28|->s22, s28|->s23, s28|->s25, s28|->s27, s29|->s1, s29|->s2, s29|->s5, s29|->s6, s29|->s7, s29|->s12, s29|->s15, s29|->s16, s29|->s20, s29|->s25, s29|->s26, s29|->s28, s30|->s0, s30|->s3, s30|->s5, s30|->s8, s30|->s9, s30|->s10, s30|->s14, s30|->s16, s30|->s17, s30|->s18, s30|->s20, s30|->s26, s30|->s28, s31|->s0, s31|->s1, s31|->s2, s31|->s3, s31|->s5, s31|->s7, s31|->s8, s31|->s13, s31|->s14, s31|->s17, s31|->s18, s31|->s19, s31|->s21, s31|->s25, s31|->s27, s31|->s29, s32|->s1, s32|->s6, s32|->s7, s32|->s9, s32|->s11, s32|->s12, s32|->s13, s32|->s17, s32|->s19, s32|->s21, s32|->s22, s32|->s24, s32|->s25, s32|->s26, s32|->s29, s33|->s2, s33|->s3, s33|->s7, s33|->s10, s33|->s15, s33|->s18, s33|->s20, s33|->s22, s33|->s23, s33|->s26, s33|->s27, s33|->s28, s33|->s29, s33|->s30, s33|->s31, s33|->s32, s34|->s0, s34|->s1, s34|->s2, s34|->s4, s34|->s6, s34|->s7, s34|->s8, s34|->s9, s34|->s10, s34|->s11, s34|->s12, s34|->s14, s34|->s16, s34|->s18, s34|->s20, s34|->s25, s34|->s27, s34|->s28, s34|->s30, s35|->s0, s35|->s1, s35|->s3, s35|->s5, s35|->s6, s35|->s9, s35|->s11, s35|->s14, s35|->s16, s35|->s17, s35|->s19, s35|->s20, s35|->s22, s35|->s23, s35|->s24, s35|->s27, s35|->s28, s35|->s32, s35|->s33, s36|->s0, s36|->s1, s36|->s3, s36|->s4, s36|->s5, s36|->s6, s36|->s11, s36|->s14, s36|->s15, s36|->s17, s36|->s21, s36|->s22, s36|->s23, s36|->s25, s36|->s28, s36|->s31, s36|->s35, s37|->s1, s37|->s2, s37|->s5, s37|->s6, s37|->s7, s37|->s8, s37|->s9, s37|->s11, s37|->s12, s37|->s16, s37|->s17, s37|->s18, s37|->s20, s37|->s21, s37|->s24, s37|->s25, s37|->s28, s37|->s29, s37|->s30, s37|->s31, s37|->s32} &
    e_res={r1|->r0, r4|->r0, r4|->r1, r4|->r3, r5|->r0, r5|->r1, r5|->r4, r6|->r4, r7|->r4, r7|->r6, r8|->r3, r8|->r4, r8|->r5, r9|->r2, r9|->r5, r9|->r6, r9|->r7, r10|->r0, r10|->r1, r10|->r3, r10|->r4, r10|->r5, r10|->r8, r10|->r9, r11|->r2, r11|->r3, r11|->r4, r11|->r7, r11|->r8, r11|->r9, r11|->r10, r12|->r0, r12|->r1, r12|->r2, r12|->r4, r12|->r5, r12|->r6, r12|->r9, r12|->r10, r12|->r11, r13|->r0, r13|->r1, r13|->r2, r13|->r4, r13|->r8, r13|->r9, r13|->r11, r13|->r12, r14|->r6, r14|->r7, r14|->r8, r14|->r9, r14|->r12, r15|->r0, r15|->r3, r15|->r5, r15|->r10, r15|->r11, r15|->r13, r15|->r14, r16|->r3, r16|->r5, r16|->r6, r16|->r7, r16|->r8, r16|->r10, r16|->r11, r16|->r14, r17|->r1, r17|->r2, r17|->r3, r17|->r5, r17|->r6, r17|->r7, r17|->r8, r17|->r10, r17|->r11, r17|->r12, r17|->r13, r17|->r16, r18|->r0, r18|->r1, r18|->r2, r18|->r3, r18|->r8, r18|->r10, r18|->r11, r18|->r12, r18|->r13, r18|->r15, r18|->r16, r19|->r1, r19|->r3, r19|->r4, r19|->r5, r19|->r9, r19|->r13, r19|->r14, r19|->r16, r19|->r17, r20|->r1, r20|->r3, r20|->r4, r20|->r6, r20|->r10, r20|->r11, r20|->r12, r20|->r13, r20|->r14, r20|->r16, r20|->r17, r21|->r0, r21|->r2, r21|->r3, r21|->r4, r21|->r9, r21|->r10, r21|->r11, r21|->r12, r21|->r13, r21|->r15, r21|->r16, r21|->r17, r21|->r20, r22|->r1, r22|->r5, r22|->r7, r22|->r9, r22|->r10, r22|->r11, r22|->r16, r22|->r18, r22|->r19, r23|->r1, r23|->r5, r23|->r6, r23|->r7, r23|->r9, r23|->r10, r23|->r12, r23|->r18, r23|->r19, r23|->r21, r24|->r1, r24|->r2, r24|->r5, r24|->r7, r24|->r8, r24|->r11, r24|->r12, r24|->r13, r24|->r14, r24|->r15, r24|->r16, r24|->r18, r24|->r19, r24|->r23, r25|->r1, r25|->r2, r25|->r7, r25|->r9, r25|->r10, r25|->r11, r25|->r12, r25|->r16, r25|->r18, r25|->r19, r25|->r21, r25|->r22, r25|->r23, r26|->r1, r26|->r6, r26|->r8, r26|->r10, r26|->r12, r26|->r13, r26|->r15, r26|->r19, r26|->r25, r27|->r1, r27|->r2, r27|->r3, r27|->r4, r27|->r5, r27|->r7, r27|->r10, r27|->r11, r27|->r13, r27|->r14, r27|->r15, r27|->r19, r27|->r20, r27|->r22, r27|->r23, r28|->r2, r28|->r3, r28|->r7, r28|->r9, r28|->r13, r28|->r15, r28|->r18, r28|->r21, r28|->r22, r28|->r25, r28|->r26, r28|->r27, r29|->r1, r29|->r2, r29|->r3, r29|->r6, r29|->r7, r29|->r8, r29|->r10, r29|->r11, r29|->r12, r29|->r13, r29|->r14, r29|->r15, r29|->r16, r29|->r17, r29|->r18, r29|->r22, r29|->r25, r30|->r1, r30|->r2, r30|->r3, r30|->r4, r30|->r6, r30|->r7, r30|->r8, r30|->r9, r30|->r13, r30|->r17, r30|->r19, r30|->r20, r30|->r21, r30|->r27, r30|->r28, r31|->r0, r31|->r1, r31|->r2, r31|->r3, r31|->r4, r31|->r6, r31|->r7, r31|->r9, r31|->r11, r31|->r13, r31|->r14, r31|->r15, r31|->r19, r31|->r24, r31|->r25, r31|->r30, r32|->r0, r32|->r2, r32|->r6, r32|->r7, r32|->r12, r32|->r14, r32|->r16, r32|->r19, r32|->r21, r32|->r22, r32|->r26, r32|->r27, r32|->r28, r32|->r30, r33|->r3, r33|->r4, r33|->r5, r33|->r6, r33|->r8, r33|->r9, r33|->r13, r33|->r15, r33|->r16, r33|->r17, r33|->r20, r33|->r21, r33|->r23, r33|->r26, r33|->r28, r33|->r29, r33|->r31, r33|->r32, r34|->r3, r34|->r4, r34|->r6, r34|->r7, r34|->r12, r34|->r13, r34|->r14, r34|->r16, r34|->r22, r34|->r24, r34|->r27, r34|->r28, r34|->r30, r34|->r31, r34|->r32, r34|->r33, r35|->r1, r35|->r2, r35|->r4, r35|->r5, r35|->r6, r35|->r7, r35|->r9, r35|->r10, r35|->r12, r35|->r13, r35|->r14, r35|->r16, r35|->r20, r35|->r23, r35|->r24, r35|->r26, r35|->r27, r35|->r32, r36|->r1, r36|->r2, r36|->r3, r36|->r4, r36|->r5, r36|->r7, r36|->r8, r36|->r16, r36|->r18, r36|->r20, r36|->r21, r36|->r22, r36|->r23, r36|->r24, r36|->r25, r36|->r27, r36|->r30, r36|->r32, r36|->r34} &
    rules={rule0|->(rec(su:s6,re:r33,mo:per,pr: 0,co:{c8,c6,c3,c5,c7,c4})), rule1|->(rec(su:s30,re:r27,mo:pro,pr: 2,co:{c1,c2,c3,c4,c0,c6})), rule2|->(rec(su:s27,re:r18,mo:pro,pr: 2,co:{c3,c7,c1,c9,c2,c6})), rule3|->(rec(su:s6,re:r26,mo:per,pr: 4,co:{c1,c5,c2,c4,c6,c0,c7})), rule4|->(rec(su:s4,re:r14,mo:pro,pr: 0,co:{c5,c7,c3,c9})), rule5|->(rec(su:s37,re:r31,mo:pro,pr: 1,co:{c1,c7,c0,c3})), rule6|->(rec(su:s24,re:r15,mo:pro,pr: 1,co:{c1,c7,c4,c6,c2,c8})), rule7|->(rec(su:s3,re:r0,mo:per,pr: 1,co:{c8,c4,c6,c9,c2,c3,c5})), rule8|->(rec(su:s17,re:r16,mo:per,pr: 0,co:{c1,c2})), rule9|->(rec(su:s8,re:r6,mo:pro,pr: 1,co:{c6,c0,c8,c2})), rule10|->(rec(su:s26,re:r19,mo:per,pr: 2,co:{c2,c7,c6,c4,c3})), rule11|->(rec(su:s13,re:r4,mo:pro,pr: 0,co:{c3,c5,c4,c1})), rule12|->(rec(su:s14,re:r8,mo:per,pr: 2,co:{c3,c9,c8,c0,c2,c1}))}

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