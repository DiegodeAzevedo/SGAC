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
    e_sub={s1|->s0, s3|->s2, s4|->s0, s4|->s2, s5|->s0, s5|->s1, s5|->s3, s5|->s4, s6|->s1, s6|->s3, s6|->s5, s7|->s1, s7|->s3, s7|->s4, s7|->s5, s8|->s0, s8|->s4, s8|->s6, s8|->s7, s9|->s1, s9|->s3, s9|->s5, s9|->s7, s10|->s3, s10|->s9, s11|->s1, s11|->s3, s11|->s4, s11|->s10, s12|->s0, s12|->s1, s12|->s3, s12|->s6, s13|->s3, s13|->s8, s14|->s0, s14|->s2, s14|->s6, s14|->s7, s14|->s8, s14|->s9, s14|->s10, s14|->s11, s14|->s12, s15|->s1, s15|->s2, s15|->s6, s15|->s10, s15|->s12, s15|->s14, s16|->s0, s16|->s3, s16|->s5, s16|->s6, s16|->s7, s16|->s9, s16|->s11, s16|->s14, s17|->s0, s17|->s1, s17|->s2, s17|->s6, s17|->s7, s17|->s8, s17|->s9, s17|->s11, s17|->s13, s17|->s14, s17|->s16, s18|->s0, s18|->s1, s18|->s3, s18|->s4, s18|->s8, s18|->s10, s18|->s13, s18|->s14, s18|->s15, s18|->s16, s19|->s4, s19|->s5, s19|->s6, s19|->s10, s19|->s12, s19|->s13, s19|->s14, s20|->s0, s20|->s3, s20|->s5, s20|->s7, s20|->s10, s20|->s12, s20|->s14, s20|->s15, s21|->s1, s21|->s2, s21|->s3, s21|->s4, s21|->s10, s21|->s11, s21|->s14, s21|->s15, s21|->s18, s21|->s19, s22|->s0, s22|->s3, s22|->s4, s22|->s5, s22|->s7, s22|->s12, s22|->s13, s22|->s14, s22|->s18, s22|->s19, s22|->s21, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s5, s23|->s6, s23|->s7, s23|->s8, s23|->s9, s23|->s11, s23|->s12, s23|->s15, s23|->s16, s23|->s19, s23|->s21, s23|->s22, s24|->s4, s24|->s9, s24|->s10, s24|->s13, s24|->s14, s24|->s18, s24|->s22, s25|->s0, s25|->s1, s25|->s2, s25|->s4, s25|->s6, s25|->s9, s25|->s13, s25|->s15, s25|->s16, s25|->s17, s25|->s21, s25|->s22, s25|->s24, s26|->s0, s26|->s2, s26|->s3, s26|->s4, s26|->s5, s26|->s11, s26|->s12, s26|->s16, s26|->s17, s26|->s18, s26|->s19, s26|->s20, s26|->s22, s26|->s24, s26|->s25, s27|->s0, s27|->s1, s27|->s5, s27|->s7, s27|->s8, s27|->s14, s27|->s16, s27|->s18, s27|->s19, s27|->s22, s27|->s24, s27|->s25, s27|->s26, s28|->s1, s28|->s2, s28|->s4, s28|->s6, s28|->s8, s28|->s9, s28|->s11, s28|->s12, s28|->s13, s28|->s15, s28|->s17, s28|->s20, s28|->s22, s28|->s23, s28|->s25, s28|->s27, s29|->s0, s29|->s3, s29|->s4, s29|->s5, s29|->s9, s29|->s13, s29|->s14, s29|->s16, s29|->s17, s29|->s18, s29|->s20, s29|->s21, s29|->s24, s29|->s25, s29|->s26, s29|->s28, s30|->s6, s30|->s7, s30|->s8, s30|->s9, s30|->s10, s30|->s11, s30|->s12, s30|->s13, s30|->s14, s30|->s16, s30|->s17, s30|->s19, s30|->s21, s30|->s25, s30|->s26, s30|->s27, s30|->s29, s31|->s1, s31|->s3, s31|->s4, s31|->s6, s31|->s7, s31|->s9, s31|->s12, s31|->s16, s31|->s17, s31|->s20, s31|->s22, s31|->s24, s31|->s27, s31|->s28, s31|->s30, s32|->s0, s32|->s1, s32|->s3, s32|->s6, s32|->s7, s32|->s8, s32|->s9, s32|->s15, s32|->s18, s32|->s20, s32|->s21, s32|->s28, s32|->s30, s32|->s31, s33|->s1, s33|->s5, s33|->s11, s33|->s17, s33|->s23, s33|->s25, s33|->s30, s33|->s32, s34|->s0, s34|->s1, s34|->s6, s34|->s11, s34|->s13, s34|->s18, s34|->s24, s34|->s27, s34|->s30, s34|->s32, s34|->s33} &
    e_res={r2|->r0, r2|->r1, r3|->r0, r3|->r2, r4|->r0, r5|->r3, r6|->r1, r6|->r2, r6|->r3, r6|->r4, r7|->r0, r8|->r0, r8|->r2, r8|->r3, r8|->r6, r8|->r7, r9|->r0, r9|->r2, r9|->r3, r9|->r4, r9|->r5, r9|->r6, r9|->r8, r10|->r0, r10|->r2, r10|->r3, r10|->r5, r10|->r8, r11|->r0, r11|->r1, r11|->r2, r11|->r4, r11|->r5, r11|->r7, r11|->r8, r11|->r9, r11|->r10, r12|->r1, r12|->r4, r12|->r6, r12|->r7, r12|->r8, r12|->r9, r12|->r10, r12|->r11, r13|->r10, r13|->r12, r14|->r0, r14|->r1, r14|->r2, r14|->r3, r14|->r4, r14|->r5, r14|->r8, r14|->r9, r14|->r10, r14|->r11, r15|->r0, r15|->r2, r15|->r5, r15|->r7, r15|->r8, r15|->r10, r15|->r12, r15|->r14, r16|->r0, r16|->r2, r16|->r3, r16|->r5, r16|->r6, r16|->r8, r16|->r9, r16|->r10, r16|->r11, r16|->r12, r16|->r13, r17|->r0, r17|->r3, r17|->r4, r17|->r6, r17|->r8, r17|->r13, r17|->r15, r17|->r16, r18|->r3, r18|->r7, r18|->r14, r19|->r1, r19|->r2, r19|->r7, r19|->r9, r19|->r12, r19|->r13, r19|->r14, r19|->r15, r20|->r1, r20|->r4, r20|->r8, r20|->r9, r20|->r10, r20|->r11, r20|->r15, r20|->r16, r20|->r17, r20|->r19, r21|->r3, r21|->r4, r21|->r5, r21|->r6, r21|->r7, r21|->r9, r21|->r11, r21|->r12, r21|->r14, r21|->r15, r21|->r17, r21|->r19, r22|->r0, r22|->r1, r22|->r3, r22|->r5, r22|->r6, r22|->r10, r22|->r11, r22|->r12, r22|->r13, r22|->r17, r22|->r18, r22|->r19, r22|->r20, r22|->r21, r23|->r2, r23|->r3, r23|->r4, r23|->r5, r23|->r6, r23|->r9, r23|->r10, r23|->r13, r23|->r14, r23|->r15, r23|->r17, r23|->r18, r23|->r19, r23|->r21, r24|->r1, r24|->r5, r24|->r7, r24|->r9, r24|->r10, r24|->r12, r24|->r13, r24|->r15, r24|->r18, r24|->r19, r24|->r20, r24|->r21, r24|->r22, r25|->r5, r25|->r6, r25|->r7, r25|->r8, r25|->r9, r25|->r10, r25|->r11, r25|->r13, r25|->r14, r25|->r16, r25|->r18, r25|->r19, r25|->r21, r25|->r23, r25|->r24, r26|->r0, r26|->r1, r26|->r2, r26|->r3, r26|->r6, r26|->r7, r26|->r11, r26|->r12, r26|->r13, r26|->r14, r26|->r16, r26|->r19, r26|->r24, r26|->r25, r27|->r0, r27|->r2, r27|->r4, r27|->r6, r27|->r7, r27|->r8, r27|->r10, r27|->r12, r27|->r14, r27|->r15, r27|->r17, r27|->r19, r27|->r21, r27|->r24, r28|->r1, r28|->r3, r28|->r4, r28|->r5, r28|->r10, r28|->r12, r28|->r15, r28|->r16, r28|->r19, r28|->r20, r28|->r21, r28|->r23, r29|->r0, r29|->r1, r29|->r4, r29|->r5, r29|->r9, r29|->r13, r29|->r15, r29|->r16, r29|->r18, r29|->r20, r29|->r21, r29|->r22, r29|->r23, r29|->r24, r29|->r26, r29|->r27, r30|->r0, r30|->r1, r30|->r2, r30|->r4, r30|->r7, r30|->r9, r30|->r10, r30|->r11, r30|->r12, r30|->r13, r30|->r14, r30|->r15, r30|->r18, r30|->r19, r30|->r22, r30|->r23, r30|->r24, r30|->r25, r30|->r26, r30|->r29, r31|->r0, r31|->r4, r31|->r7, r31|->r9, r31|->r15, r31|->r16, r31|->r21, r31|->r28, r31|->r29, r32|->r1, r32|->r5, r32|->r6, r32|->r8, r32|->r9, r32|->r13, r32|->r15, r32|->r16, r32|->r18, r32|->r23, r32|->r24, r32|->r25, r32|->r27, r32|->r31, r33|->r1, r33|->r10, r33|->r11, r33|->r12, r33|->r13, r33|->r14, r33|->r15, r33|->r16, r33|->r17, r33|->r19, r33|->r21, r33|->r22, r33|->r26, r33|->r27, r34|->r0, r34|->r1, r34|->r2, r34|->r5, r34|->r6, r34|->r7, r34|->r9, r34|->r10, r34|->r11, r34|->r12, r34|->r13, r34|->r20, r34|->r22, r34|->r23, r34|->r25, r34|->r28} &
    rules={rule0|->(rec(su:s21,re:r13,mo:per,pr: 0,co:{c2})), rule1|->(rec(su:s12,re:r12,mo:pro,pr: 1,co:{c5,c2,c7,c4})), rule2|->(rec(su:s28,re:r8,mo:per,pr: 3,co:{c3,c6,c4,c5})), rule3|->(rec(su:s24,re:r27,mo:per,pr: 2,co:{c2,c5,c6,c0,c7,c4,c9})), rule4|->(rec(su:s2,re:r27,mo:per,pr: 0,co:{c2,c4,c6})), rule5|->(rec(su:s14,re:r14,mo:pro,pr: 2,co:{c1,c3})), rule6|->(rec(su:s25,re:r10,mo:per,pr: 0,co:{c8,c3,c0,c6,c9,c7})), rule7|->(rec(su:s17,re:r28,mo:pro,pr: 0,co:{c0,c4,c3,c5})), rule8|->(rec(su:s2,re:r18,mo:per,pr: 1,co:{c6,c0,c2,c7,c3,c4})), rule9|->(rec(su:s24,re:r20,mo:pro,pr: 0,co:{c3,c0,c1,c2,c8})), rule10|->(rec(su:s27,re:r33,mo:per,pr: 4,co:{c1,c0,c3,c9})), rule11|->(rec(su:s3,re:r26,mo:pro,pr: 3,co:{c4,c0,c2,c7})), rule12|->(rec(su:s23,re:r22,mo:per,pr: 3,co:{c2,c4,c3}))}

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