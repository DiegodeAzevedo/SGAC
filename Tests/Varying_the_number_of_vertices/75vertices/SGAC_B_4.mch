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
    e_sub={s1|->s0, s2|->s0, s3|->s0, s3|->s1, s5|->s0, s5|->s3, s5|->s4, s6|->s0, s6|->s4, s7|->s0, s7|->s2, s7|->s3, s7|->s6, s8|->s0, s8|->s1, s8|->s3, s8|->s4, s8|->s6, s8|->s7, s9|->s1, s9|->s2, s9|->s4, s9|->s5, s9|->s6, s9|->s8, s10|->s1, s10|->s2, s10|->s5, s10|->s7, s11|->s3, s11|->s4, s11|->s7, s11|->s8, s11|->s9, s12|->s2, s12|->s3, s12|->s5, s12|->s9, s13|->s0, s13|->s1, s13|->s3, s13|->s4, s13|->s5, s13|->s7, s13|->s9, s14|->s1, s14|->s5, s14|->s8, s14|->s11, s14|->s12, s15|->s0, s15|->s7, s15|->s8, s15|->s10, s15|->s11, s15|->s13, s15|->s14, s16|->s0, s16|->s1, s16|->s2, s16|->s3, s16|->s5, s16|->s6, s16|->s8, s16|->s11, s16|->s15, s17|->s1, s17|->s2, s17|->s4, s17|->s5, s17|->s11, s17|->s13, s17|->s15, s18|->s0, s18|->s1, s18|->s3, s18|->s4, s18|->s6, s18|->s7, s18|->s9, s18|->s11, s18|->s12, s18|->s13, s18|->s14, s18|->s15, s19|->s0, s19|->s1, s19|->s5, s19|->s6, s19|->s8, s19|->s10, s19|->s11, s19|->s14, s19|->s15, s19|->s16, s19|->s17, s19|->s18, s20|->s0, s20|->s1, s20|->s4, s20|->s6, s20|->s9, s20|->s15, s20|->s18, s21|->s2, s21|->s4, s21|->s6, s21|->s9, s21|->s10, s21|->s13, s21|->s15, s21|->s16, s21|->s17, s21|->s19, s21|->s20, s22|->s0, s22|->s1, s22|->s5, s22|->s6, s22|->s7, s22|->s8, s22|->s9, s22|->s11, s22|->s13, s22|->s14, s22|->s18, s22|->s20, s22|->s21, s23|->s1, s23|->s2, s23|->s3, s23|->s4, s23|->s6, s23|->s8, s23|->s12, s23|->s13, s23|->s14, s23|->s15, s23|->s17, s23|->s18, s23|->s19, s23|->s20, s24|->s0, s24|->s1, s24|->s2, s24|->s5, s24|->s7, s24|->s10, s24|->s12, s24|->s13, s24|->s14, s24|->s18, s24|->s19, s24|->s22, s25|->s1, s25|->s3, s25|->s8, s25|->s10, s25|->s11, s25|->s13, s25|->s16, s25|->s17, s25|->s18, s25|->s20, s25|->s21, s25|->s22, s25|->s23, s26|->s2, s26|->s3, s26|->s7, s26|->s12, s26|->s16, s26|->s18, s26|->s20, s26|->s23, s27|->s0, s27|->s3, s27|->s4, s27|->s5, s27|->s6, s27|->s7, s27|->s9, s27|->s10, s27|->s11, s27|->s12, s27|->s16, s27|->s17, s27|->s23, s27|->s24, s27|->s25, s27|->s26, s28|->s0, s28|->s1, s28|->s3, s28|->s4, s28|->s7, s28|->s9, s28|->s10, s28|->s13, s28|->s19, s28|->s21, s28|->s26, s28|->s27, s29|->s1, s29|->s2, s29|->s3, s29|->s7, s29|->s8, s29|->s10, s29|->s11, s29|->s15, s29|->s19, s29|->s21, s29|->s22, s29|->s23, s29|->s24, s29|->s25, s29|->s27, s29|->s28, s30|->s0, s30|->s1, s30|->s5, s30|->s7, s30|->s8, s30|->s9, s30|->s13, s30|->s17, s30|->s18, s30|->s21, s30|->s24, s30|->s27, s31|->s0, s31|->s2, s31|->s3, s31|->s4, s31|->s5, s31|->s6, s31|->s7, s31|->s8, s31|->s9, s31|->s10, s31|->s11, s31|->s15, s31|->s17, s31|->s20, s31|->s21, s31|->s22, s31|->s24, s31|->s27, s31|->s29, s31|->s30, s32|->s2, s32|->s6, s32|->s9, s32|->s10, s32|->s12, s32|->s16, s32|->s19, s32|->s20, s32|->s22, s32|->s25, s32|->s27, s32|->s28, s33|->s1, s33|->s2, s33|->s3, s33|->s4, s33|->s6, s33|->s9, s33|->s10, s33|->s11, s33|->s13, s33|->s17, s33|->s18, s33|->s20, s33|->s23, s33|->s27, s33|->s28, s33|->s30, s33|->s32, s34|->s0, s34|->s3, s34|->s4, s34|->s5, s34|->s7, s34|->s9, s34|->s10, s34|->s13, s34|->s14, s34|->s17, s34|->s18, s34|->s19, s34|->s20, s34|->s22, s34|->s24, s34|->s26, s34|->s28, s34|->s29, s34|->s31, s34|->s32, s35|->s0, s35|->s4, s35|->s5, s35|->s6, s35|->s8, s35|->s9, s35|->s10, s35|->s11, s35|->s12, s35|->s20, s35|->s21, s35|->s23, s35|->s26, s35|->s27, s35|->s30, s35|->s31, s35|->s32, s35|->s33, s36|->s0, s36|->s1, s36|->s2, s36|->s4, s36|->s8, s36|->s9, s36|->s11, s36|->s13, s36|->s15, s36|->s16, s36|->s17, s36|->s18, s36|->s19, s36|->s20, s36|->s21, s36|->s22, s36|->s24, s36|->s26, s36|->s27, s36|->s28, s36|->s29, s36|->s33, s37|->s0, s37|->s2, s37|->s3, s37|->s5, s37|->s6, s37|->s9, s37|->s10, s37|->s12, s37|->s14, s37|->s15, s37|->s17, s37|->s19, s37|->s24, s37|->s26, s37|->s28, s37|->s29, s37|->s30, s37|->s31, s37|->s32, s37|->s34, s37|->s35} &
    e_res={r2|->r0, r2|->r1, r3|->r1, r3|->r2, r4|->r0, r4|->r2, r4|->r3, r5|->r0, r5|->r4, r6|->r0, r6|->r5, r7|->r0, r7|->r4, r7|->r5, r7|->r6, r8|->r3, r8|->r4, r8|->r5, r8|->r7, r9|->r2, r9|->r4, r9|->r5, r9|->r6, r10|->r0, r10|->r1, r10|->r6, r10|->r9, r11|->r1, r11|->r2, r11|->r5, r11|->r6, r12|->r0, r12|->r1, r12|->r2, r12|->r4, r12|->r5, r12|->r7, r12|->r9, r13|->r2, r13|->r9, r13|->r10, r13|->r11, r14|->r0, r14|->r1, r14|->r4, r14|->r5, r14|->r8, r14|->r9, r14|->r10, r14|->r11, r14|->r12, r14|->r13, r15|->r1, r15|->r4, r15|->r5, r15|->r6, r15|->r7, r15|->r9, r15|->r11, r15|->r14, r16|->r0, r16|->r1, r16|->r4, r16|->r5, r16|->r6, r16|->r7, r16|->r8, r16|->r9, r16|->r12, r16|->r15, r17|->r4, r17|->r5, r17|->r12, r17|->r14, r17|->r15, r17|->r16, r18|->r0, r18|->r4, r18|->r5, r18|->r7, r18|->r8, r18|->r12, r18|->r13, r18|->r14, r18|->r15, r18|->r16, r19|->r0, r19|->r2, r19|->r4, r19|->r7, r19|->r8, r19|->r9, r19|->r10, r19|->r12, r19|->r15, r19|->r17, r19|->r18, r20|->r0, r20|->r1, r20|->r5, r20|->r7, r20|->r9, r20|->r11, r20|->r12, r20|->r13, r20|->r14, r20|->r16, r20|->r17, r20|->r18, r20|->r19, r21|->r0, r21|->r1, r21|->r2, r21|->r5, r21|->r8, r21|->r12, r21|->r13, r21|->r14, r21|->r15, r21|->r17, r21|->r20, r22|->r0, r22|->r1, r22|->r4, r22|->r5, r22|->r8, r22|->r15, r22|->r16, r22|->r17, r22|->r18, r22|->r19, r22|->r21, r23|->r2, r23|->r3, r23|->r4, r23|->r5, r23|->r7, r23|->r10, r23|->r11, r23|->r13, r23|->r15, r23|->r16, r24|->r4, r24|->r7, r24|->r9, r24|->r10, r24|->r13, r24|->r16, r24|->r17, r24|->r21, r24|->r22, r25|->r0, r25|->r5, r25|->r7, r25|->r8, r25|->r9, r25|->r15, r25|->r16, r25|->r19, r25|->r20, r25|->r21, r25|->r23, r25|->r24, r26|->r1, r26|->r6, r26|->r9, r26|->r10, r26|->r15, r26|->r16, r26|->r17, r26|->r18, r26|->r19, r26|->r24, r27|->r0, r27|->r5, r27|->r6, r27|->r7, r27|->r8, r27|->r11, r27|->r12, r27|->r16, r27|->r17, r27|->r19, r27|->r21, r27|->r22, r27|->r23, r27|->r24, r28|->r2, r28|->r3, r28|->r6, r28|->r11, r28|->r12, r28|->r14, r28|->r16, r28|->r18, r28|->r23, r28|->r24, r28|->r27, r29|->r1, r29|->r3, r29|->r4, r29|->r5, r29|->r7, r29|->r8, r29|->r9, r29|->r10, r29|->r13, r29|->r14, r29|->r15, r29|->r17, r29|->r18, r29|->r19, r29|->r21, r29|->r26, r30|->r2, r30|->r3, r30|->r5, r30|->r7, r30|->r8, r30|->r11, r30|->r12, r30|->r15, r30|->r18, r30|->r19, r30|->r20, r30|->r22, r30|->r23, r30|->r24, r30|->r25, r30|->r26, r30|->r27, r31|->r0, r31|->r1, r31|->r4, r31|->r6, r31|->r7, r31|->r8, r31|->r12, r31|->r13, r31|->r14, r31|->r16, r31|->r17, r31|->r26, r31|->r28, r31|->r29, r32|->r0, r32|->r4, r32|->r6, r32|->r7, r32|->r14, r32|->r16, r32|->r18, r32|->r19, r32|->r20, r32|->r22, r32|->r23, r32|->r24, r32|->r25, r32|->r26, r32|->r28, r32|->r31, r33|->r0, r33|->r3, r33|->r6, r33|->r7, r33|->r9, r33|->r10, r33|->r12, r33|->r14, r33|->r18, r33|->r20, r33|->r21, r33|->r23, r33|->r24, r33|->r25, r33|->r27, r33|->r29, r33|->r30, r34|->r0, r34|->r1, r34|->r2, r34|->r3, r34|->r4, r34|->r6, r34|->r10, r34|->r12, r34|->r15, r34|->r16, r34|->r20, r34|->r21, r34|->r23, r34|->r24, r34|->r26, r34|->r28, r35|->r1, r35|->r2, r35|->r3, r35|->r4, r35|->r7, r35|->r8, r35|->r9, r35|->r14, r35|->r16, r35|->r18, r35|->r20, r35|->r22, r35|->r23, r35|->r24, r35|->r29, r35|->r31, r35|->r32, r36|->r1, r36|->r2, r36|->r5, r36|->r7, r36|->r10, r36|->r13, r36|->r14, r36|->r19, r36|->r20, r36|->r21, r36|->r26, r36|->r29} &
    rules={rule0|->(rec(su:s33,re:r15,mo:pro,pr: 4,co:{c4,c1,c6,c5,c7})), rule1|->(rec(su:s25,re:r15,mo:pro,pr: 2,co:{c1,c8,c9,c7,c2,c0})), rule2|->(rec(su:s19,re:r3,mo:per,pr: 1,co:{c0,c1,c3,c5,c8})), rule3|->(rec(su:s6,re:r12,mo:pro,pr: 4,co:{c9,c5,c3,c4,c7,c6,c1,c2})), rule4|->(rec(su:s25,re:r24,mo:pro,pr: 0,co:{c2,c0,c3,c8})), rule5|->(rec(su:s6,re:r2,mo:per,pr: 4,co:{c3})), rule6|->(rec(su:s10,re:r9,mo:pro,pr: 1,co:{c2,c4,c9,c7,c8})), rule7|->(rec(su:s29,re:r12,mo:per,pr: 2,co:{c4,c0,c6,c3})), rule8|->(rec(su:s21,re:r24,mo:per,pr: 3,co:{c4,c0,c1})), rule9|->(rec(su:s18,re:r36,mo:per,pr: 1,co:{c0,c3,c6,c1,c7,c9})), rule10|->(rec(su:s26,re:r23,mo:per,pr: 3,co:{c2,c5,c8,c4})), rule11|->(rec(su:s14,re:r28,mo:per,pr: 0,co:{c7,c0,c1,c4,c3,c8,c9})), rule12|->(rec(su:s11,re:r24,mo:pro,pr: 1,co:{c4}))}

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