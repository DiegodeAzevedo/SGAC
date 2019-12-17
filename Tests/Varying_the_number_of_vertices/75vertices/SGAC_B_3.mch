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
    e_sub={s2|->s0, s3|->s2, s4|->s1, s4|->s3, s5|->s1, s5|->s2, s5|->s3, s6|->s0, s6|->s5, s7|->s0, s7|->s2, s7|->s3, s7|->s4, s8|->s0, s8|->s1, s8|->s2, s8|->s4, s8|->s5, s8|->s7, s9|->s1, s9|->s2, s9|->s3, s9|->s4, s9|->s5, s9|->s7, s9|->s8, s10|->s0, s10|->s2, s10|->s5, s10|->s6, s10|->s8, s11|->s0, s11|->s7, s12|->s2, s12|->s3, s12|->s5, s12|->s6, s12|->s7, s12|->s8, s12|->s10, s13|->s0, s13|->s1, s13|->s2, s13|->s3, s13|->s6, s13|->s8, s13|->s11, s13|->s12, s14|->s0, s14|->s1, s14|->s2, s14|->s3, s14|->s4, s14|->s6, s14|->s7, s14|->s8, s14|->s9, s14|->s10, s14|->s11, s14|->s12, s15|->s1, s15|->s2, s15|->s5, s15|->s6, s15|->s8, s15|->s9, s15|->s10, s15|->s12, s15|->s14, s16|->s0, s16|->s1, s16|->s6, s16|->s7, s16|->s9, s16|->s12, s16|->s14, s16|->s15, s17|->s0, s17|->s1, s17|->s3, s17|->s6, s17|->s9, s17|->s10, s17|->s12, s17|->s13, s17|->s14, s17|->s16, s18|->s5, s18|->s9, s18|->s10, s18|->s12, s18|->s13, s18|->s14, s18|->s15, s19|->s0, s19|->s2, s19|->s3, s19|->s5, s19|->s6, s19|->s7, s19|->s8, s19|->s9, s19|->s10, s19|->s12, s19|->s15, s19|->s17, s19|->s18, s20|->s1, s20|->s3, s20|->s5, s20|->s6, s20|->s13, s20|->s14, s20|->s15, s20|->s17, s20|->s19, s21|->s1, s21|->s4, s21|->s11, s21|->s12, s21|->s14, s21|->s16, s21|->s17, s21|->s19, s22|->s3, s22|->s6, s22|->s7, s22|->s8, s22|->s10, s22|->s11, s22|->s16, s22|->s17, s22|->s19, s22|->s20, s23|->s2, s23|->s3, s23|->s6, s23|->s8, s23|->s13, s23|->s15, s23|->s16, s23|->s17, s23|->s18, s23|->s21, s23|->s22, s24|->s1, s24|->s2, s24|->s3, s24|->s7, s24|->s9, s24|->s10, s24|->s11, s24|->s12, s24|->s17, s24|->s19, s24|->s20, s24|->s21, s25|->s1, s25|->s2, s25|->s3, s25|->s4, s25|->s5, s25|->s6, s25|->s9, s25|->s12, s25|->s15, s25|->s16, s25|->s18, s25|->s19, s25|->s21, s25|->s23, s25|->s24, s26|->s1, s26|->s2, s26|->s6, s26|->s8, s26|->s9, s26|->s10, s26|->s14, s26|->s15, s26|->s16, s26|->s18, s26|->s20, s26|->s21, s27|->s0, s27|->s1, s27|->s4, s27|->s6, s27|->s7, s27|->s10, s27|->s12, s27|->s16, s27|->s17, s27|->s20, s27|->s25, s27|->s26, s28|->s0, s28|->s1, s28|->s2, s28|->s3, s28|->s4, s28|->s6, s28|->s7, s28|->s10, s28|->s11, s28|->s17, s28|->s18, s28|->s21, s28|->s22, s28|->s24, s28|->s27, s29|->s1, s29|->s2, s29|->s4, s29|->s5, s29|->s7, s29|->s9, s29|->s11, s29|->s14, s29|->s15, s29|->s16, s29|->s18, s29|->s20, s29|->s21, s29|->s22, s29|->s26, s29|->s27, s29|->s28, s30|->s1, s30|->s4, s30|->s6, s30|->s7, s30|->s10, s30|->s11, s30|->s12, s30|->s20, s30|->s28, s31|->s0, s31|->s1, s31|->s3, s31|->s7, s31|->s8, s31|->s9, s31|->s11, s31|->s12, s31|->s14, s31|->s15, s31|->s20, s31|->s21, s31|->s22, s31|->s25, s31|->s30, s32|->s2, s32|->s5, s32|->s7, s32|->s11, s32|->s12, s32|->s15, s32|->s20, s32|->s22, s32|->s23, s32|->s24, s32|->s27, s32|->s28, s32|->s29, s32|->s30, s33|->s3, s33|->s5, s33|->s6, s33|->s11, s33|->s14, s33|->s17, s33|->s20, s33|->s21, s33|->s25, s33|->s26, s33|->s28, s33|->s29, s33|->s32, s34|->s1, s34|->s3, s34|->s4, s34|->s5, s34|->s7, s34|->s9, s34|->s10, s34|->s11, s34|->s12, s34|->s14, s34|->s17, s34|->s18, s34|->s20, s34|->s23, s34|->s24, s34|->s26, s34|->s27, s34|->s33, s35|->s2, s35|->s3, s35|->s7, s35|->s10, s35|->s11, s35|->s13, s35|->s14, s35|->s15, s35|->s18, s35|->s20, s35|->s22, s35|->s23, s35|->s26, s35|->s27, s35|->s30, s35|->s32, s36|->s0, s36|->s1, s36|->s2, s36|->s5, s36|->s6, s36|->s7, s36|->s9, s36|->s10, s36|->s13, s36|->s14, s36|->s16, s36|->s17, s36|->s21, s36|->s22, s36|->s23, s36|->s25, s36|->s26, s36|->s27, s36|->s29, s36|->s33, s36|->s34, s37|->s1, s37|->s3, s37|->s4, s37|->s9, s37|->s11, s37|->s12, s37|->s13, s37|->s16, s37|->s17, s37|->s18, s37|->s20, s37|->s21, s37|->s23, s37|->s25, s37|->s27, s37|->s29, s37|->s30, s37|->s31, s37|->s33, s37|->s34, s37|->s36} &
    e_res={r2|->r1, r3|->r0, r3|->r1, r4|->r2, r5|->r3, r6|->r1, r6|->r2, r6|->r3, r6|->r4, r7|->r0, r7|->r3, r7|->r5, r8|->r6, r9|->r0, r9|->r2, r9|->r6, r9|->r7, r9|->r8, r10|->r0, r10|->r1, r10|->r5, r11|->r0, r11|->r1, r11|->r4, r11|->r5, r11|->r6, r11|->r7, r11|->r10, r12|->r0, r12|->r1, r12|->r6, r12|->r8, r13|->r0, r13|->r2, r13|->r3, r13|->r5, r13|->r7, r13|->r8, r13|->r9, r13|->r10, r13|->r11, r14|->r0, r14|->r1, r14|->r2, r14|->r7, r14|->r9, r15|->r0, r15|->r1, r15|->r8, r15|->r13, r16|->r1, r16|->r2, r16|->r4, r16|->r5, r16|->r6, r16|->r8, r16|->r10, r17|->r0, r17|->r1, r17|->r2, r17|->r7, r17|->r8, r17|->r11, r17|->r15, r17|->r16, r18|->r0, r18|->r1, r18|->r2, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r7, r18|->r8, r18|->r10, r18|->r11, r18|->r14, r18|->r16, r19|->r1, r19|->r2, r19|->r3, r19|->r5, r19|->r6, r19|->r7, r19|->r10, r19|->r11, r19|->r13, r19|->r17, r19|->r18, r20|->r0, r20|->r6, r20|->r7, r20|->r8, r20|->r9, r20|->r11, r20|->r16, r21|->r1, r21|->r3, r21|->r4, r21|->r6, r21|->r8, r21|->r10, r21|->r13, r21|->r14, r21|->r15, r21|->r16, r21|->r18, r21|->r19, r21|->r20, r22|->r0, r22|->r1, r22|->r2, r22|->r4, r22|->r6, r22|->r11, r22|->r13, r22|->r15, r22|->r17, r22|->r18, r22|->r19, r22|->r20, r22|->r21, r23|->r0, r23|->r3, r23|->r4, r23|->r5, r23|->r8, r23|->r14, r23|->r16, r23|->r17, r23|->r20, r23|->r21, r23|->r22, r24|->r6, r24|->r7, r24|->r8, r24|->r10, r24|->r12, r24|->r13, r24|->r14, r24|->r16, r24|->r18, r24|->r22, r24|->r23, r25|->r5, r25|->r6, r25|->r8, r25|->r10, r25|->r11, r25|->r12, r25|->r23, r26|->r0, r26|->r2, r26|->r3, r26|->r4, r26|->r6, r26|->r7, r26|->r8, r26|->r9, r26|->r10, r26|->r11, r26|->r13, r26|->r19, r26|->r20, r26|->r22, r26|->r23, r26|->r24, r27|->r0, r27|->r1, r27|->r6, r27|->r7, r27|->r8, r27|->r9, r27|->r10, r27|->r14, r27|->r15, r27|->r16, r27|->r17, r27|->r19, r27|->r20, r27|->r22, r27|->r23, r28|->r1, r28|->r2, r28|->r3, r28|->r12, r28|->r14, r28|->r16, r28|->r19, r28|->r23, r28|->r24, r28|->r26, r28|->r27, r29|->r0, r29|->r1, r29|->r5, r29|->r6, r29|->r8, r29|->r9, r29|->r13, r29|->r15, r29|->r17, r29|->r22, r29|->r23, r29|->r24, r29|->r25, r29|->r26, r29|->r27, r30|->r0, r30|->r1, r30|->r2, r30|->r3, r30|->r7, r30|->r9, r30|->r10, r30|->r14, r30|->r15, r30|->r16, r30|->r23, r30|->r25, r30|->r27, r30|->r28, r30|->r29, r31|->r1, r31|->r2, r31|->r3, r31|->r7, r31|->r8, r31|->r11, r31|->r12, r31|->r14, r31|->r17, r31|->r20, r31|->r21, r31|->r24, r31|->r27, r31|->r29, r32|->r5, r32|->r6, r32|->r7, r32|->r8, r32|->r11, r32|->r12, r32|->r13, r32|->r15, r32|->r16, r32|->r17, r32|->r18, r32|->r20, r32|->r22, r32|->r23, r32|->r25, r32|->r26, r32|->r27, r32|->r30, r32|->r31, r33|->r0, r33|->r1, r33|->r2, r33|->r3, r33|->r4, r33|->r9, r33|->r11, r33|->r13, r33|->r14, r33|->r15, r33|->r17, r33|->r19, r33|->r21, r33|->r24, r33|->r25, r33|->r26, r33|->r27, r33|->r28, r33|->r29, r33|->r31, r34|->r0, r34|->r1, r34|->r2, r34|->r6, r34|->r10, r34|->r11, r34|->r12, r34|->r14, r34|->r16, r34|->r17, r34|->r21, r34|->r22, r34|->r24, r34|->r26, r34|->r27, r34|->r29, r34|->r31, r34|->r32, r35|->r1, r35|->r2, r35|->r3, r35|->r4, r35|->r5, r35|->r6, r35|->r7, r35|->r8, r35|->r11, r35|->r13, r35|->r15, r35|->r16, r35|->r20, r35|->r21, r35|->r23, r35|->r26, r35|->r28, r35|->r29, r35|->r30, r35|->r31, r35|->r32, r35|->r33, r35|->r34, r36|->r0, r36|->r3, r36|->r5, r36|->r6, r36|->r8, r36|->r9, r36|->r10, r36|->r11, r36|->r16, r36|->r18, r36|->r19, r36|->r21, r36|->r23, r36|->r24, r36|->r26, r36|->r28, r36|->r29, r36|->r30, r36|->r32, r36|->r33} &
    rules={rule0|->(rec(su:s19,re:r0,mo:pro,pr: 4,co:{c7,c6,c8,c5,c2})), rule1|->(rec(su:s3,re:r31,mo:pro,pr: 3,co:{c0,c5,c4})), rule2|->(rec(su:s36,re:r25,mo:pro,pr: 4,co:{c3,c0,c8,c5,c4,c6,c7})), rule3|->(rec(su:s27,re:r26,mo:per,pr: 1,co:{c0,c7,c6,c5})), rule4|->(rec(su:s37,re:r32,mo:per,pr: 0,co:{c5,c9})), rule5|->(rec(su:s15,re:r7,mo:pro,pr: 4,co:{c5})), rule6|->(rec(su:s15,re:r28,mo:pro,pr: 4,co:{c0,c6,c2,c1,c4,c5})), rule7|->(rec(su:s33,re:r27,mo:per,pr: 3,co:{c9,c0,c5,c8,c3})), rule8|->(rec(su:s17,re:r11,mo:per,pr: 4,co:{c6,c9,c2,c3,c7})), rule9|->(rec(su:s18,re:r22,mo:pro,pr: 3,co:{c3,c2,c6,c5,c9,c0})), rule10|->(rec(su:s18,re:r1,mo:pro,pr: 0,co:{c5,c2,c3,c8})), rule11|->(rec(su:s30,re:r8,mo:per,pr: 0,co:{c8,c6,c0,c5,c3,c4})), rule12|->(rec(su:s16,re:r12,mo:per,pr: 3,co:{c3,c0,c7,c1,c5,c4}))}

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