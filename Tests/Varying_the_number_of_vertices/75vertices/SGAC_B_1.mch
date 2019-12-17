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
    e_sub={s2|->s0, s2|->s1, s4|->s0, s4|->s1, s4|->s2, s4|->s3, s5|->s0, s5|->s1, s5|->s2, s6|->s0, s6|->s4, s6|->s5, s7|->s3, s8|->s3, s8|->s6, s9|->s0, s9|->s3, s9|->s6, s10|->s0, s10|->s3, s10|->s7, s10|->s9, s11|->s2, s11|->s3, s11|->s5, s11|->s7, s11|->s8, s11|->s10, s12|->s0, s12|->s3, s12|->s5, s12|->s7, s12|->s8, s13|->s3, s13|->s6, s13|->s7, s14|->s0, s14|->s1, s14|->s2, s14|->s4, s14|->s5, s14|->s8, s14|->s9, s14|->s13, s15|->s1, s15|->s3, s15|->s5, s15|->s6, s15|->s12, s15|->s14, s16|->s0, s16|->s1, s16|->s2, s16|->s3, s16|->s4, s16|->s6, s16|->s7, s16|->s9, s16|->s10, s16|->s11, s16|->s12, s16|->s13, s16|->s14, s17|->s2, s17|->s4, s17|->s10, s17|->s15, s17|->s16, s18|->s0, s18|->s3, s18|->s5, s18|->s6, s18|->s7, s18|->s10, s18|->s12, s18|->s14, s18|->s16, s19|->s3, s19|->s7, s19|->s12, s19|->s15, s19|->s16, s20|->s3, s20|->s4, s20|->s5, s20|->s6, s20|->s7, s20|->s8, s20|->s12, s20|->s13, s20|->s15, s20|->s16, s20|->s18, s20|->s19, s21|->s0, s21|->s1, s21|->s2, s21|->s4, s21|->s5, s21|->s6, s21|->s7, s21|->s10, s21|->s13, s21|->s15, s21|->s16, s21|->s17, s22|->s1, s22|->s4, s22|->s5, s22|->s6, s22|->s9, s22|->s12, s22|->s13, s22|->s14, s22|->s16, s22|->s18, s22|->s19, s22|->s20, s22|->s21, s23|->s2, s23|->s3, s23|->s4, s23|->s6, s23|->s7, s23|->s10, s23|->s12, s23|->s13, s23|->s14, s23|->s18, s23|->s19, s23|->s20, s23|->s22, s24|->s0, s24|->s1, s24|->s2, s24|->s3, s24|->s6, s24|->s8, s24|->s9, s24|->s10, s24|->s11, s24|->s13, s24|->s15, s24|->s17, s24|->s18, s24|->s21, s24|->s23, s25|->s0, s25|->s2, s25|->s3, s25|->s5, s25|->s7, s25|->s8, s25|->s9, s25|->s16, s25|->s17, s25|->s18, s25|->s19, s26|->s0, s26|->s7, s26|->s13, s26|->s15, s26|->s16, s26|->s18, s26|->s20, s26|->s23, s26|->s24, s27|->s0, s27|->s2, s27|->s3, s27|->s4, s27|->s6, s27|->s8, s27|->s9, s27|->s10, s27|->s11, s27|->s14, s27|->s15, s27|->s18, s27|->s19, s27|->s20, s27|->s21, s27|->s22, s28|->s2, s28|->s3, s28|->s6, s28|->s11, s28|->s12, s28|->s13, s28|->s14, s28|->s17, s28|->s19, s28|->s25, s28|->s26, s28|->s27, s29|->s0, s29|->s3, s29|->s5, s29|->s6, s29|->s10, s29|->s13, s29|->s14, s29|->s15, s29|->s16, s29|->s17, s29|->s18, s29|->s24, s29|->s25, s29|->s26, s29|->s27, s30|->s0, s30|->s2, s30|->s3, s30|->s8, s30|->s13, s30|->s15, s30|->s16, s30|->s17, s30|->s19, s30|->s20, s30|->s27, s30|->s28, s31|->s0, s31|->s3, s31|->s5, s31|->s10, s31|->s12, s31|->s15, s31|->s16, s31|->s17, s31|->s18, s31|->s19, s31|->s20, s31|->s21, s31|->s25, s31|->s26, s31|->s27, s31|->s29, s31|->s30, s32|->s0, s32|->s1, s32|->s2, s32|->s3, s32|->s4, s32|->s5, s32|->s6, s32|->s7, s32|->s9, s32|->s10, s32|->s12, s32|->s14, s32|->s15, s32|->s16, s32|->s17, s32|->s18, s32|->s22, s32|->s23, s32|->s24, s32|->s26, s32|->s28, s33|->s2, s33|->s4, s33|->s5, s33|->s6, s33|->s7, s33|->s14, s33|->s16, s33|->s19, s33|->s20, s33|->s21, s33|->s24, s33|->s25, s33|->s26, s33|->s28, s33|->s29, s33|->s31, s33|->s32, s34|->s2, s34|->s3, s34|->s11, s34|->s18, s34|->s19, s34|->s23, s34|->s24, s34|->s25, s34|->s27, s34|->s31, s34|->s32, s34|->s33, s35|->s0, s35|->s3, s35|->s4, s35|->s7, s35|->s10, s35|->s11, s35|->s15, s35|->s18, s35|->s21, s35|->s22, s35|->s27, s35|->s28, s35|->s29, s35|->s30, s35|->s31, s35|->s33, s35|->s34, s36|->s0, s36|->s2, s36|->s5, s36|->s6, s36|->s7, s36|->s8, s36|->s9, s36|->s10, s36|->s12, s36|->s13, s36|->s15, s36|->s16, s36|->s18, s36|->s19, s36|->s22, s36|->s23, s36|->s25, s36|->s28, s36|->s29, s36|->s30, s36|->s33, s37|->s1, s37|->s2, s37|->s5, s37|->s8, s37|->s11, s37|->s12, s37|->s14, s37|->s15, s37|->s18, s37|->s21, s37|->s22, s37|->s24, s37|->s25, s37|->s27, s37|->s28, s37|->s29, s37|->s33, s37|->s36} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r3|->r2, r4|->r3, r5|->r4, r6|->r0, r6|->r1, r6|->r2, r6|->r3, r6|->r5, r7|->r5, r8|->r4, r8|->r7, r9|->r0, r9|->r3, r9|->r6, r9|->r8, r10|->r1, r10|->r3, r10|->r4, r10|->r6, r10|->r7, r10|->r9, r11|->r3, r11|->r7, r11|->r8, r11|->r10, r12|->r0, r12|->r2, r12|->r3, r12|->r4, r12|->r11, r13|->r0, r13|->r2, r13|->r3, r13|->r4, r13|->r5, r13|->r6, r13|->r8, r13|->r10, r13|->r11, r14|->r0, r14|->r1, r14|->r4, r14|->r12, r15|->r0, r15|->r1, r15|->r2, r15|->r3, r15|->r5, r15|->r11, r15|->r13, r16|->r1, r16|->r2, r16|->r3, r16|->r5, r16|->r9, r16|->r10, r16|->r12, r16|->r13, r16|->r14, r16|->r15, r17|->r0, r17|->r7, r17|->r13, r17|->r14, r17|->r15, r18|->r0, r18|->r1, r18|->r4, r18|->r5, r18|->r12, r18|->r13, r18|->r16, r19|->r1, r19|->r4, r19|->r5, r19|->r7, r19|->r8, r19|->r9, r19|->r10, r19|->r13, r20|->r0, r20|->r2, r20|->r3, r20|->r9, r20|->r10, r20|->r11, r20|->r14, r20|->r15, r20|->r17, r20|->r19, r21|->r0, r21|->r1, r21|->r3, r21|->r4, r21|->r5, r21|->r6, r21|->r8, r21|->r11, r21|->r14, r21|->r17, r21|->r18, r21|->r20, r22|->r2, r22|->r5, r22|->r6, r22|->r7, r22|->r9, r22|->r13, r22|->r16, r22|->r17, r23|->r0, r23|->r2, r23|->r6, r23|->r7, r23|->r13, r23|->r17, r23|->r18, r23|->r19, r23|->r20, r23|->r21, r23|->r22, r24|->r1, r24|->r3, r24|->r4, r24|->r5, r24|->r6, r24|->r9, r24|->r11, r24|->r12, r24|->r19, r24|->r21, r24|->r22, r24|->r23, r25|->r1, r25|->r2, r25|->r3, r25|->r6, r25|->r8, r25|->r12, r25|->r21, r25|->r22, r25|->r23, r25|->r24, r26|->r0, r26|->r4, r26|->r5, r26|->r7, r26|->r14, r26|->r17, r26|->r18, r26|->r21, r26|->r22, r26|->r23, r26|->r24, r27|->r0, r27|->r1, r27|->r2, r27|->r4, r27|->r5, r27|->r7, r27|->r10, r27|->r13, r27|->r15, r27|->r16, r27|->r18, r27|->r20, r27|->r22, r27|->r26, r28|->r1, r28|->r3, r28|->r4, r28|->r10, r28|->r11, r28|->r15, r28|->r17, r28|->r18, r28|->r19, r28|->r21, r28|->r22, r28|->r24, r28|->r26, r29|->r2, r29|->r4, r29|->r8, r29|->r10, r29|->r11, r29|->r14, r29|->r15, r29|->r18, r29|->r20, r29|->r21, r29|->r23, r29|->r24, r29|->r25, r29|->r26, r29|->r27, r29|->r28, r30|->r0, r30|->r5, r30|->r6, r30|->r7, r30|->r8, r30|->r10, r30|->r11, r30|->r13, r30|->r15, r30|->r16, r30|->r17, r30|->r20, r30|->r21, r30|->r22, r30|->r24, r30|->r26, r30|->r27, r30|->r28, r31|->r0, r31|->r2, r31|->r3, r31|->r4, r31|->r9, r31|->r10, r31|->r11, r31|->r13, r31|->r14, r31|->r20, r31|->r22, r31|->r23, r31|->r29, r32|->r0, r32|->r5, r32|->r6, r32|->r9, r32|->r10, r32|->r11, r32|->r15, r32|->r18, r32|->r20, r32|->r21, r32|->r23, r32|->r24, r32|->r26, r32|->r28, r32|->r31, r33|->r3, r33|->r6, r33|->r8, r33|->r9, r33|->r10, r33|->r12, r33|->r13, r33|->r14, r33|->r16, r33|->r19, r33|->r23, r33|->r25, r33|->r28, r33|->r31, r33|->r32, r34|->r1, r34|->r3, r34|->r4, r34|->r7, r34|->r9, r34|->r13, r34|->r18, r34|->r19, r34|->r20, r34|->r23, r34|->r26, r34|->r27, r34|->r28, r34|->r29, r34|->r32, r34|->r33, r35|->r1, r35|->r2, r35|->r3, r35|->r5, r35|->r7, r35|->r9, r35|->r10, r35|->r13, r35|->r14, r35|->r16, r35|->r17, r35|->r21, r35|->r23, r35|->r25, r35|->r27, r35|->r28, r35|->r29, r35|->r30, r35|->r31, r35|->r32, r36|->r0, r36|->r1, r36|->r3, r36|->r4, r36|->r6, r36|->r8, r36|->r11, r36|->r12, r36|->r13, r36|->r14, r36|->r16, r36|->r20, r36|->r21, r36|->r24, r36|->r25, r36|->r26, r36|->r27, r36|->r29, r36|->r32, r36|->r33} &
    rules={rule0|->(rec(su:s32,re:r25,mo:pro,pr: 2,co:{c3,c5,c8,c2,c7,c9})), rule1|->(rec(su:s10,re:r26,mo:pro,pr: 0,co:{c9,c5,c6})), rule2|->(rec(su:s11,re:r6,mo:per,pr: 0,co:{c0,c7,c2,c6,c3,c9,c4})), rule3|->(rec(su:s19,re:r24,mo:per,pr: 3,co:{c7,c3,c9,c5})), rule4|->(rec(su:s11,re:r22,mo:pro,pr: 2,co:{c7,c1,c4,c5,c2})), rule5|->(rec(su:s23,re:r19,mo:pro,pr: 4,co:{c1,c0,c4})), rule6|->(rec(su:s8,re:r16,mo:per,pr: 2,co:{c8,c9,c1,c6})), rule7|->(rec(su:s25,re:r36,mo:pro,pr: 4,co:{c2,c7,c0,c9})), rule8|->(rec(su:s0,re:r18,mo:per,pr: 4,co:{c3,c2,c7,c4,c6,c8,c9})), rule9|->(rec(su:s36,re:r29,mo:pro,pr: 1,co:{c8,c4,c7,c9,c0,c5})), rule10|->(rec(su:s31,re:r10,mo:pro,pr: 3,co:{c3,c5,c0,c4,c9,c8})), rule11|->(rec(su:s28,re:r33,mo:pro,pr: 3,co:{c8,c7})), rule12|->(rec(su:s20,re:r31,mo:pro,pr: 3,co:{c8,c5,c7,c6}))}

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