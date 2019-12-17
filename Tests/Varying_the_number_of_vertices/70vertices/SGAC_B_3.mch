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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34};
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
    e_sub={s4|->s0, s4|->s2, s4|->s3, s5|->s0, s5|->s2, s5|->s3, s6|->s3, s6|->s5, s7|->s0, s7|->s1, s7|->s2, s7|->s4, s7|->s5, s8|->s0, s8|->s4, s8|->s7, s9|->s0, s9|->s6, s10|->s3, s10|->s6, s10|->s7, s10|->s8, s11|->s0, s11|->s1, s11|->s2, s11|->s3, s11|->s5, s11|->s6, s11|->s8, s11|->s9, s11|->s10, s12|->s0, s12|->s2, s12|->s10, s13|->s3, s13|->s6, s13|->s7, s13|->s11, s14|->s1, s14|->s3, s14|->s4, s14|->s7, s14|->s8, s14|->s11, s15|->s4, s15|->s5, s15|->s10, s15|->s12, s16|->s0, s16|->s1, s16|->s2, s16|->s3, s16|->s4, s16|->s7, s16|->s8, s16|->s14, s16|->s15, s17|->s2, s17|->s3, s17|->s4, s17|->s6, s17|->s7, s17|->s8, s17|->s11, s17|->s12, s17|->s14, s17|->s15, s18|->s0, s18|->s1, s18|->s3, s18|->s6, s18|->s10, s18|->s12, s18|->s14, s18|->s15, s18|->s16, s18|->s17, s19|->s0, s19|->s3, s19|->s8, s19|->s11, s19|->s12, s19|->s13, s19|->s14, s19|->s15, s19|->s17, s20|->s0, s20|->s2, s20|->s3, s20|->s5, s20|->s6, s20|->s7, s20|->s8, s20|->s10, s20|->s13, s20|->s16, s20|->s18, s20|->s19, s21|->s4, s21|->s5, s21|->s7, s21|->s8, s21|->s10, s21|->s11, s21|->s12, s21|->s13, s21|->s15, s21|->s16, s21|->s17, s21|->s18, s21|->s20, s22|->s0, s22|->s2, s22|->s4, s22|->s6, s22|->s7, s22|->s10, s22|->s11, s22|->s20, s23|->s0, s23|->s1, s23|->s2, s23|->s4, s23|->s6, s23|->s7, s23|->s9, s23|->s10, s23|->s11, s23|->s14, s23|->s15, s23|->s16, s23|->s20, s24|->s5, s24|->s6, s24|->s7, s24|->s8, s24|->s12, s24|->s14, s24|->s17, s24|->s18, s24|->s21, s24|->s23, s25|->s0, s25|->s1, s25|->s5, s25|->s6, s25|->s7, s25|->s9, s25|->s13, s25|->s14, s25|->s16, s25|->s18, s25|->s19, s25|->s21, s25|->s22, s25|->s24, s26|->s0, s26|->s4, s26|->s6, s26|->s7, s26|->s8, s26|->s9, s26|->s10, s26|->s11, s26|->s17, s26|->s18, s26|->s19, s26|->s24, s26|->s25, s27|->s3, s27|->s5, s27|->s6, s27|->s7, s27|->s8, s27|->s9, s27|->s11, s27|->s12, s27|->s13, s27|->s14, s27|->s17, s27|->s18, s27|->s19, s27|->s20, s27|->s21, s27|->s22, s27|->s24, s27|->s26, s28|->s2, s28|->s4, s28|->s8, s28|->s10, s28|->s11, s28|->s13, s28|->s14, s28|->s15, s28|->s16, s28|->s17, s28|->s18, s28|->s23, s28|->s25, s28|->s27, s29|->s5, s29|->s11, s29|->s12, s29|->s16, s29|->s17, s29|->s20, s29|->s21, s29|->s23, s29|->s25, s29|->s27, s29|->s28, s30|->s1, s30|->s2, s30|->s3, s30|->s5, s30|->s10, s30|->s11, s30|->s14, s30|->s16, s30|->s18, s30|->s19, s30|->s20, s30|->s21, s30|->s23, s30|->s27, s30|->s28, s31|->s2, s31|->s5, s31|->s7, s31|->s12, s31|->s13, s31|->s15, s31|->s19, s31|->s20, s31|->s21, s31|->s23, s31|->s24, s31|->s25, s32|->s0, s32|->s1, s32|->s5, s32|->s7, s32|->s17, s32|->s19, s32|->s20, s32|->s27, s32|->s29, s32|->s30, s32|->s31, s33|->s0, s33|->s2, s33|->s3, s33|->s5, s33|->s10, s33|->s12, s33|->s14, s33|->s15, s33|->s16, s33|->s18, s33|->s19, s33|->s20, s33|->s24, s33|->s29, s34|->s1, s34|->s2, s34|->s4, s34|->s5, s34|->s6, s34|->s7, s34|->s10, s34|->s13, s34|->s15, s34|->s16, s34|->s17, s34|->s19, s34|->s20, s34|->s22, s34|->s25, s34|->s26, s34|->s27, s34|->s30, s34|->s31} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r3|->r0, r3|->r2, r4|->r1, r4|->r2, r5|->r0, r6|->r1, r6|->r4, r6|->r5, r7|->r1, r7|->r4, r7|->r5, r7|->r6, r8|->r0, r8|->r1, r8|->r4, r8|->r6, r9|->r3, r9|->r4, r9|->r5, r9|->r6, r9|->r7, r10|->r0, r10|->r1, r10|->r2, r10|->r3, r10|->r6, r10|->r7, r10|->r8, r11|->r1, r11|->r2, r11|->r3, r11|->r4, r11|->r7, r11|->r8, r11|->r9, r11|->r10, r12|->r0, r12|->r2, r12|->r3, r12|->r7, r12|->r9, r12|->r10, r13|->r3, r13|->r6, r13|->r7, r13|->r11, r13|->r12, r14|->r1, r14|->r6, r14|->r7, r14|->r10, r14|->r11, r15|->r0, r15|->r1, r15|->r3, r15|->r4, r15|->r5, r15|->r6, r15|->r7, r15|->r9, r15|->r10, r15|->r11, r15|->r12, r15|->r13, r16|->r0, r16|->r1, r16|->r2, r16|->r5, r16|->r7, r16|->r9, r16|->r10, r17|->r0, r17|->r1, r17|->r2, r17|->r3, r17|->r5, r17|->r9, r17|->r11, r17|->r14, r18|->r2, r18|->r3, r18|->r6, r18|->r9, r18|->r10, r18|->r11, r18|->r15, r18|->r16, r18|->r17, r19|->r0, r19|->r1, r19|->r4, r19|->r6, r19|->r10, r19|->r12, r19|->r13, r19|->r14, r19|->r15, r19|->r16, r19|->r18, r20|->r0, r20|->r1, r20|->r3, r20|->r4, r20|->r10, r20|->r11, r20|->r12, r20|->r18, r21|->r1, r21|->r2, r21|->r3, r21|->r5, r21|->r6, r21|->r8, r21|->r9, r21|->r12, r21|->r16, r21|->r17, r21|->r18, r21|->r19, r22|->r1, r22|->r3, r22|->r4, r22|->r10, r22|->r13, r22|->r14, r22|->r16, r22|->r18, r22|->r19, r22|->r20, r23|->r0, r23|->r1, r23|->r2, r23|->r3, r23|->r5, r23|->r6, r23|->r7, r23|->r8, r23|->r9, r23|->r11, r23|->r14, r23|->r15, r23|->r17, r23|->r18, r23|->r19, r23|->r22, r24|->r0, r24|->r1, r24|->r2, r24|->r4, r24|->r6, r24|->r8, r24|->r10, r24|->r11, r24|->r13, r24|->r15, r24|->r17, r24|->r19, r24|->r21, r24|->r22, r25|->r0, r25|->r1, r25|->r2, r25|->r4, r25|->r5, r25|->r6, r25|->r7, r25|->r8, r25|->r9, r25|->r10, r25|->r13, r25|->r14, r25|->r15, r25|->r17, r25|->r18, r25|->r19, r25|->r20, r25|->r21, r26|->r0, r26|->r3, r26|->r4, r26|->r5, r26|->r6, r26|->r7, r26|->r8, r26|->r9, r26|->r10, r26|->r11, r26|->r14, r26|->r15, r26|->r18, r26|->r20, r26|->r21, r26|->r23, r26|->r24, r27|->r1, r27|->r2, r27|->r4, r27|->r8, r27|->r9, r27|->r10, r27|->r11, r27|->r12, r27|->r16, r27|->r17, r27|->r19, r27|->r21, r27|->r25, r27|->r26, r28|->r1, r28|->r3, r28|->r4, r28|->r6, r28|->r8, r28|->r9, r28|->r10, r28|->r11, r28|->r12, r28|->r13, r28|->r19, r28|->r23, r28|->r24, r28|->r26, r28|->r27, r29|->r1, r29|->r3, r29|->r5, r29|->r9, r29|->r11, r29|->r12, r29|->r13, r29|->r14, r29|->r16, r29|->r17, r29|->r19, r29|->r20, r29|->r21, r29|->r24, r30|->r7, r30|->r9, r30|->r10, r30|->r14, r30|->r16, r30|->r17, r30|->r21, r30|->r23, r30|->r24, r30|->r28, r30|->r29, r31|->r9, r31|->r13, r31|->r18, r31|->r19, r31|->r20, r31|->r22, r31|->r23, r32|->r6, r32|->r8, r32|->r9, r32|->r11, r32|->r13, r32|->r15, r32|->r16, r32|->r17, r32|->r19, r32|->r22, r32|->r24, r32|->r27, r32|->r29, r32|->r30, r33|->r0, r33|->r2, r33|->r4, r33|->r7, r33|->r9, r33|->r10, r33|->r13, r33|->r15, r33|->r17, r33|->r20, r33|->r24, r33|->r27, r33|->r28, r33|->r29, r34|->r0, r34|->r2, r34|->r5, r34|->r7, r34|->r11, r34|->r13, r34|->r14, r34|->r16, r34|->r18, r34|->r21, r34|->r24, r34|->r27, r34|->r28, r34|->r29, r34|->r30} &
    rules={rule0|->(rec(su:s8,re:r3,mo:per,pr: 0,co:{c3,c7,c8})), rule1|->(rec(su:s22,re:r21,mo:pro,pr: 2,co:{c6,c5,c8,c7,c9,c4,c0})), rule2|->(rec(su:s8,re:r17,mo:pro,pr: 1,co:{c3,c1})), rule3|->(rec(su:s34,re:r27,mo:pro,pr: 0,co:{c4,c9,c8,c5})), rule4|->(rec(su:s31,re:r12,mo:pro,pr: 1,co:{c5,c8,c3,c9})), rule5|->(rec(su:s21,re:r16,mo:per,pr: 2,co:{c9,c7})), rule6|->(rec(su:s21,re:r32,mo:pro,pr: 4,co:{c2,c5,c6,c0,c1})), rule7|->(rec(su:s13,re:r27,mo:pro,pr: 3,co:{c1,c6,c3,c5,c0})), rule8|->(rec(su:s7,re:r2,mo:per,pr: 0,co:{c7,c5,c8,c2})), rule9|->(rec(su:s18,re:r6,mo:per,pr: 3,co:{c4})), rule10|->(rec(su:s25,re:r21,mo:per,pr: 0,co:{c3,c9,c8,c0,c1,c2,c4})), rule11|->(rec(su:s12,re:r10,mo:pro,pr: 1,co:{c3,c8,c0,c6,c5})), rule12|->(rec(su:s21,re:r34,mo:pro,pr: 0,co:{c7}))}

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