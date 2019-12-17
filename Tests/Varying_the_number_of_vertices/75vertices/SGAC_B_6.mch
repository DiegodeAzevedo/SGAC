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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s3|->s1, s4|->s1, s5|->s2, s5|->s3, s5|->s4, s6|->s2, s6|->s3, s7|->s2, s8|->s1, s8|->s2, s8|->s4, s8|->s7, s9|->s0, s9|->s5, s9|->s6, s10|->s1, s10|->s2, s10|->s3, s10|->s6, s10|->s9, s11|->s4, s11|->s5, s11|->s7, s11|->s8, s11|->s9, s11|->s10, s12|->s0, s12|->s1, s12|->s5, s12|->s6, s12|->s7, s12|->s8, s12|->s9, s12|->s11, s13|->s2, s13|->s6, s13|->s8, s13|->s10, s14|->s1, s14|->s2, s14|->s3, s14|->s7, s14|->s8, s14|->s9, s14|->s10, s14|->s11, s14|->s12, s15|->s2, s15|->s5, s15|->s6, s15|->s9, s15|->s12, s15|->s13, s16|->s2, s16|->s3, s16|->s15, s17|->s2, s17|->s3, s17|->s5, s17|->s6, s17|->s7, s17|->s8, s17|->s9, s17|->s10, s17|->s14, s17|->s16, s18|->s0, s18|->s1, s18|->s4, s18|->s5, s18|->s6, s18|->s7, s18|->s8, s18|->s10, s18|->s11, s18|->s13, s18|->s14, s18|->s15, s18|->s16, s18|->s17, s19|->s0, s19|->s2, s19|->s3, s19|->s6, s19|->s7, s19|->s8, s19|->s10, s19|->s11, s19|->s15, s19|->s16, s19|->s17, s20|->s0, s20|->s1, s20|->s3, s20|->s4, s20|->s5, s20|->s7, s20|->s11, s20|->s14, s20|->s16, s20|->s18, s20|->s19, s21|->s3, s21|->s5, s21|->s6, s21|->s8, s21|->s9, s21|->s13, s21|->s16, s21|->s17, s21|->s19, s21|->s20, s22|->s0, s22|->s3, s22|->s5, s22|->s11, s22|->s12, s22|->s14, s22|->s16, s22|->s18, s22|->s20, s22|->s21, s23|->s0, s23|->s1, s23|->s3, s23|->s4, s23|->s5, s23|->s8, s23|->s10, s23|->s11, s23|->s12, s23|->s14, s23|->s16, s23|->s18, s23|->s19, s23|->s21, s24|->s0, s24|->s1, s24|->s3, s24|->s7, s24|->s8, s24|->s9, s24|->s12, s24|->s14, s24|->s17, s24|->s22, s24|->s23, s25|->s1, s25|->s2, s25|->s5, s25|->s6, s25|->s12, s25|->s14, s25|->s15, s25|->s17, s25|->s19, s25|->s21, s25|->s24, s26|->s3, s26|->s4, s26|->s5, s26|->s6, s26|->s7, s26|->s8, s26|->s10, s26|->s12, s26|->s16, s26|->s17, s26|->s21, s26|->s22, s26|->s23, s26|->s24, s27|->s0, s27|->s3, s27|->s5, s27|->s14, s27|->s16, s27|->s17, s27|->s20, s27|->s21, s28|->s0, s28|->s1, s28|->s3, s28|->s4, s28|->s7, s28|->s8, s28|->s9, s28|->s10, s28|->s11, s28|->s13, s28|->s14, s28|->s16, s28|->s17, s28|->s19, s28|->s22, s28|->s23, s28|->s26, s29|->s0, s29|->s2, s29|->s3, s29|->s4, s29|->s6, s29|->s7, s29|->s10, s29|->s11, s29|->s14, s29|->s16, s29|->s17, s29|->s20, s29|->s21, s29|->s22, s29|->s23, s29|->s26, s29|->s27, s29|->s28, s30|->s0, s30|->s1, s30|->s4, s30|->s7, s30|->s10, s30|->s11, s30|->s12, s30|->s14, s30|->s15, s30|->s19, s30|->s20, s30|->s22, s30|->s24, s30|->s25, s30|->s26, s30|->s28, s31|->s0, s31|->s1, s31|->s3, s31|->s4, s31|->s7, s31|->s10, s31|->s11, s31|->s14, s31|->s16, s31|->s17, s31|->s22, s31|->s24, s31|->s26, s31|->s27, s31|->s28, s32|->s0, s32|->s2, s32|->s3, s32|->s4, s32|->s5, s32|->s9, s32|->s10, s32|->s13, s32|->s14, s32|->s15, s32|->s16, s32|->s18, s32|->s19, s32|->s21, s32|->s22, s32|->s23, s32|->s27, s32|->s29, s33|->s1, s33|->s3, s33|->s7, s33|->s9, s33|->s10, s33|->s12, s33|->s13, s33|->s16, s33|->s19, s33|->s22, s33|->s23, s33|->s24, s33|->s25, s33|->s27, s33|->s29, s33|->s30, s34|->s0, s34|->s5, s34|->s9, s34|->s11, s34|->s13, s34|->s18, s34|->s22, s34|->s23, s34|->s26, s34|->s29, s34|->s30, s35|->s0, s35|->s1, s35|->s4, s35|->s5, s35|->s6, s35|->s7, s35|->s10, s35|->s11, s35|->s12, s35|->s17, s35|->s20, s35|->s21, s35|->s22, s35|->s23, s35|->s25, s35|->s26, s35|->s28, s35|->s30, s35|->s32, s35|->s33, s36|->s0, s36|->s1, s36|->s2, s36|->s5, s36|->s6, s36|->s10, s36|->s11, s36|->s13, s36|->s14, s36|->s17, s36|->s20, s36|->s23, s36|->s26, s36|->s27, s36|->s29, s36|->s30, s36|->s32, s36|->s35, s37|->s3, s37|->s9, s37|->s11, s37|->s13, s37|->s17, s37|->s19, s37|->s21, s37|->s22, s37|->s25, s37|->s26, s37|->s29, s37|->s30, s37|->s32, s37|->s33, s37|->s35, s37|->s36} &
    e_res={r3|->r0, r3|->r1, r3|->r2, r4|->r1, r4|->r3, r5|->r0, r5|->r1, r5|->r4, r6|->r0, r6|->r4, r7|->r0, r7|->r1, r7|->r2, r7|->r3, r7|->r5, r7|->r6, r8|->r2, r8|->r6, r8|->r7, r9|->r0, r9|->r1, r9|->r2, r9|->r4, r9|->r6, r9|->r8, r10|->r0, r10|->r5, r11|->r0, r11|->r4, r11|->r5, r12|->r0, r12|->r1, r12|->r5, r12|->r7, r12|->r8, r12|->r9, r13|->r1, r13|->r4, r13|->r7, r14|->r0, r14|->r1, r14|->r3, r14|->r4, r14|->r6, r14|->r7, r14|->r8, r14|->r9, r14|->r11, r14|->r12, r14|->r13, r15|->r2, r15|->r3, r15|->r5, r15|->r7, r15|->r8, r15|->r9, r15|->r10, r15|->r11, r15|->r13, r16|->r1, r16|->r2, r16|->r8, r16|->r9, r16|->r11, r16|->r12, r16|->r13, r16|->r15, r17|->r0, r17|->r1, r17|->r4, r17|->r6, r17|->r7, r17|->r9, r17|->r10, r17|->r11, r17|->r15, r18|->r0, r18|->r2, r18|->r4, r18|->r6, r18|->r7, r18|->r8, r18|->r10, r18|->r12, r18|->r13, r18|->r16, r18|->r17, r19|->r0, r19|->r1, r19|->r2, r19|->r4, r19|->r8, r19|->r9, r19|->r10, r19|->r16, r19|->r17, r19|->r18, r20|->r1, r20|->r3, r20|->r5, r20|->r6, r20|->r7, r20|->r9, r20|->r10, r20|->r14, r20|->r15, r20|->r16, r20|->r17, r20|->r18, r20|->r19, r21|->r0, r21|->r2, r21|->r3, r21|->r5, r21|->r7, r21|->r8, r21|->r9, r21|->r10, r21|->r12, r21|->r13, r21|->r14, r21|->r16, r21|->r17, r21|->r18, r21|->r19, r21|->r20, r22|->r0, r22|->r1, r22|->r2, r22|->r3, r22|->r4, r22|->r7, r22|->r11, r22|->r12, r22|->r14, r22|->r16, r22|->r19, r22|->r20, r23|->r0, r23|->r2, r23|->r3, r23|->r9, r23|->r10, r23|->r11, r23|->r12, r23|->r13, r23|->r16, r23|->r17, r23|->r19, r23|->r20, r24|->r0, r24|->r1, r24|->r2, r24|->r4, r24|->r5, r24|->r6, r24|->r8, r24|->r11, r24|->r12, r24|->r14, r24|->r16, r24|->r18, r24|->r22, r24|->r23, r25|->r0, r25|->r2, r25|->r5, r25|->r8, r25|->r10, r25|->r11, r25|->r12, r25|->r15, r25|->r17, r25|->r19, r25|->r20, r25|->r21, r25|->r22, r26|->r0, r26|->r2, r26|->r5, r26|->r6, r26|->r8, r26|->r10, r26|->r15, r26|->r17, r26|->r18, r26|->r19, r26|->r20, r26|->r21, r26|->r22, r26|->r24, r27|->r0, r27|->r3, r27|->r4, r27|->r7, r27|->r8, r27|->r12, r27|->r13, r27|->r14, r27|->r17, r27|->r18, r27|->r19, r27|->r20, r27|->r22, r27|->r23, r27|->r25, r28|->r1, r28|->r7, r28|->r8, r28|->r9, r28|->r10, r28|->r11, r28|->r12, r28|->r14, r28|->r17, r28|->r19, r28|->r20, r28|->r22, r28|->r23, r28|->r24, r28|->r25, r29|->r0, r29|->r2, r29|->r3, r29|->r4, r29|->r7, r29|->r10, r29|->r11, r29|->r13, r29|->r15, r29|->r16, r29|->r17, r29|->r18, r29|->r21, r29|->r22, r29|->r23, r29|->r25, r29|->r26, r30|->r0, r30|->r5, r30|->r7, r30|->r8, r30|->r9, r30|->r10, r30|->r11, r30|->r12, r30|->r15, r30|->r17, r30|->r18, r30|->r21, r30|->r26, r30|->r27, r31|->r0, r31|->r8, r31|->r11, r31|->r12, r31|->r13, r31|->r15, r31|->r16, r31|->r18, r31|->r20, r31|->r23, r31|->r26, r31|->r27, r31|->r28, r31|->r30, r32|->r1, r32|->r2, r32|->r3, r32|->r5, r32|->r6, r32|->r8, r32|->r9, r32|->r19, r32|->r20, r32|->r22, r32|->r23, r32|->r24, r32|->r25, r32|->r28, r32|->r30, r33|->r0, r33|->r3, r33|->r4, r33|->r5, r33|->r11, r33|->r13, r33|->r15, r33|->r16, r33|->r17, r33|->r23, r33|->r24, r33|->r26, r33|->r28, r33|->r32, r34|->r1, r34|->r2, r34|->r6, r34|->r9, r34|->r11, r34|->r12, r34|->r13, r34|->r14, r34|->r15, r34|->r20, r34|->r23, r34|->r24, r34|->r26, r34|->r29, r34|->r30, r34|->r32, r34|->r33, r35|->r2, r35|->r3, r35|->r5, r35|->r6, r35|->r7, r35|->r8, r35|->r10, r35|->r11, r35|->r12, r35|->r13, r35|->r14, r35|->r16, r35|->r17, r35|->r23, r35|->r25, r35|->r26, r35|->r28, r35|->r29, r35|->r31, r35|->r34, r36|->r0, r36|->r1, r36|->r4, r36|->r6, r36|->r8, r36|->r10, r36|->r11, r36|->r12, r36|->r13, r36|->r14, r36|->r15, r36|->r16, r36|->r27, r36|->r28, r36|->r29, r36|->r30, r36|->r31, r36|->r32, r36|->r33, r36|->r35} &
    rules={rule0|->(rec(su:s13,re:r26,mo:pro,pr: 0,co:{c5,c6,c1,c2,c4,c9})), rule1|->(rec(su:s16,re:r36,mo:pro,pr: 3,co:{c0,c8,c3,c4})), rule2|->(rec(su:s36,re:r14,mo:per,pr: 2,co:{c9,c1,c0,c6})), rule3|->(rec(su:s36,re:r13,mo:pro,pr: 2,co:{c5,c7,c3})), rule4|->(rec(su:s1,re:r15,mo:pro,pr: 3,co:{c8,c9})), rule5|->(rec(su:s1,re:r15,mo:pro,pr: 4,co:{c3,c1})), rule6|->(rec(su:s29,re:r32,mo:per,pr: 3,co:{c3,c5,c7,c8})), rule7|->(rec(su:s28,re:r17,mo:pro,pr: 0,co:{c8,c0})), rule8|->(rec(su:s22,re:r24,mo:pro,pr: 1,co:{c5,c9,c7})), rule9|->(rec(su:s28,re:r31,mo:pro,pr: 2,co:{c3,c5,c7,c0,c8})), rule10|->(rec(su:s3,re:r19,mo:per,pr: 1,co:{c4,c8,c3,c5,c7})), rule11|->(rec(su:s29,re:r30,mo:pro,pr: 1,co:{c7,c3,c2,c1,c5,c9})), rule12|->(rec(su:s3,re:r27,mo:per,pr: 0,co:{c0,c2,c4}))}

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