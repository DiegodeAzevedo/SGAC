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
    e_sub={s1|->s0, s2|->s0, s3|->s0, s3|->s2, s4|->s2, s5|->s2, s5|->s3, s6|->s0, s6|->s2, s6|->s4, s7|->s0, s7|->s1, s7|->s6, s8|->s0, s8|->s1, s8|->s3, s8|->s5, s8|->s6, s8|->s7, s9|->s1, s9|->s2, s9|->s4, s10|->s0, s10|->s3, s10|->s4, s10|->s5, s10|->s6, s10|->s8, s10|->s9, s11|->s0, s11|->s2, s11|->s4, s11|->s5, s11|->s6, s11|->s7, s11|->s8, s12|->s2, s12|->s4, s12|->s7, s12|->s8, s13|->s1, s13|->s2, s13|->s3, s13|->s7, s13|->s8, s13|->s10, s13|->s12, s14|->s0, s14|->s3, s14|->s5, s14|->s6, s14|->s7, s14|->s8, s14|->s11, s15|->s0, s15|->s1, s15|->s3, s15|->s4, s15|->s6, s15|->s7, s15|->s10, s15|->s11, s15|->s12, s15|->s13, s16|->s0, s16|->s1, s16|->s3, s16|->s4, s16|->s7, s16|->s10, s16|->s12, s16|->s13, s16|->s14, s17|->s1, s17|->s2, s17|->s3, s17|->s4, s17|->s5, s17|->s11, s17|->s13, s17|->s14, s17|->s15, s18|->s1, s18|->s4, s18|->s9, s18|->s11, s18|->s12, s19|->s1, s19|->s2, s19|->s4, s19|->s5, s19|->s8, s19|->s12, s19|->s13, s19|->s15, s19|->s16, s20|->s3, s20|->s4, s20|->s8, s20|->s9, s20|->s12, s20|->s13, s20|->s15, s20|->s16, s20|->s18, s21|->s1, s21|->s4, s21|->s5, s21|->s7, s21|->s8, s21|->s10, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s16, s21|->s17, s21|->s20, s22|->s0, s22|->s2, s22|->s3, s22|->s5, s22|->s8, s22|->s12, s22|->s14, s22|->s16, s22|->s17, s22|->s18, s22|->s21, s23|->s2, s23|->s3, s23|->s5, s23|->s8, s23|->s11, s23|->s12, s23|->s16, s23|->s17, s23|->s18, s23|->s19, s23|->s20, s23|->s22, s24|->s0, s24|->s1, s24|->s2, s24|->s5, s24|->s6, s24|->s7, s24|->s8, s24|->s9, s24|->s11, s24|->s13, s24|->s14, s24|->s15, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s21, s24|->s23, s25|->s1, s25|->s3, s25|->s4, s25|->s5, s25|->s6, s25|->s7, s25|->s8, s25|->s9, s25|->s11, s25|->s12, s25|->s13, s25|->s15, s25|->s16, s25|->s22, s25|->s24, s26|->s3, s26|->s4, s26|->s5, s26|->s7, s26|->s9, s26|->s12, s26|->s13, s26|->s14, s26|->s15, s26|->s19, s26|->s21, s26|->s24, s26|->s25, s27|->s0, s27|->s2, s27|->s4, s27|->s6, s27|->s7, s27|->s10, s27|->s12, s27|->s13, s27|->s15, s27|->s18, s27|->s19, s27|->s21, s27|->s22, s27|->s24, s27|->s25, s28|->s3, s28|->s8, s28|->s9, s28|->s11, s28|->s15, s28|->s18, s28|->s19, s28|->s23, s28|->s24, s28|->s25, s28|->s27, s29|->s3, s29|->s4, s29|->s5, s29|->s9, s29|->s10, s29|->s12, s29|->s13, s29|->s14, s29|->s15, s29|->s18, s29|->s22, s29|->s23, s29|->s25, s29|->s27, s29|->s28, s30|->s1, s30|->s2, s30|->s3, s30|->s5, s30|->s6, s30|->s9, s30|->s10, s30|->s11, s30|->s15, s30|->s16, s30|->s22, s30|->s23, s30|->s25, s30|->s27, s30|->s29, s31|->s1, s31|->s4, s31|->s6, s31|->s8, s31|->s11, s31|->s14, s31|->s15, s31|->s16, s31|->s21, s31|->s22, s31|->s24, s31|->s29, s31|->s30, s32|->s2, s32|->s6, s32|->s7, s32|->s8, s32|->s9, s32|->s10, s32|->s12, s32|->s13, s32|->s19, s32|->s20, s32|->s21, s32|->s24, s32|->s25, s32|->s27, s33|->s0, s33|->s9, s33|->s11, s33|->s12, s33|->s14, s33|->s16, s33|->s19, s33|->s21, s33|->s22, s33|->s25, s33|->s26, s33|->s27, s33|->s29, s33|->s30, s34|->s1, s34|->s3, s34|->s4, s34|->s6, s34|->s14, s34|->s16, s34|->s17, s34|->s27, s34|->s31, s34|->s32, s34|->s33} &
    e_res={r2|->r0, r2|->r1, r3|->r0, r3|->r1, r4|->r2, r5|->r2, r5|->r3, r6|->r0, r6|->r1, r6|->r2, r6|->r5, r7|->r1, r7|->r3, r7|->r5, r8|->r0, r8|->r4, r9|->r3, r9|->r4, r9|->r7, r10|->r2, r10|->r7, r10|->r8, r10|->r9, r11|->r0, r11|->r1, r11|->r3, r11|->r5, r11|->r6, r11|->r7, r11|->r8, r11|->r9, r12|->r0, r12|->r1, r12|->r3, r12|->r4, r12|->r7, r12|->r8, r12|->r10, r13|->r0, r13|->r2, r13|->r3, r13|->r4, r13|->r5, r13|->r6, r14|->r2, r14|->r3, r14|->r7, r14|->r11, r14|->r12, r15|->r1, r15|->r4, r15|->r5, r15|->r6, r15|->r9, r15|->r13, r15|->r14, r16|->r0, r16|->r1, r16|->r3, r16|->r4, r16|->r5, r16|->r6, r16|->r7, r16|->r9, r16|->r10, r16|->r11, r16|->r12, r16|->r13, r16|->r15, r17|->r0, r17|->r1, r17|->r7, r17|->r8, r17|->r10, r17|->r11, r17|->r12, r17|->r14, r17|->r15, r17|->r16, r18|->r2, r18|->r3, r18|->r4, r18|->r7, r18|->r8, r18|->r9, r18|->r13, r18|->r15, r18|->r16, r18|->r17, r19|->r1, r19|->r3, r19|->r4, r19|->r5, r19|->r7, r19|->r8, r19|->r11, r19|->r12, r19|->r13, r19|->r14, r19|->r16, r20|->r2, r20|->r5, r20|->r6, r20|->r8, r20|->r9, r20|->r11, r20|->r12, r20|->r18, r20|->r19, r21|->r0, r21|->r1, r21|->r3, r21|->r5, r21|->r7, r21|->r8, r21|->r9, r21|->r12, r21|->r13, r21|->r20, r22|->r0, r22|->r3, r22|->r7, r22|->r8, r22|->r9, r22|->r10, r22|->r13, r22|->r16, r22|->r18, r22|->r20, r22|->r21, r23|->r0, r23|->r1, r23|->r6, r23|->r7, r23|->r9, r23|->r10, r23|->r15, r23|->r16, r23|->r21, r23|->r22, r24|->r2, r24|->r4, r24|->r5, r24|->r6, r24|->r8, r24|->r9, r24|->r10, r24|->r14, r24|->r17, r24|->r18, r24|->r19, r24|->r20, r24|->r21, r24|->r22, r25|->r2, r25|->r8, r25|->r9, r25|->r15, r25|->r16, r25|->r19, r25|->r22, r25|->r23, r25|->r24, r26|->r0, r26|->r1, r26|->r2, r26|->r3, r26|->r5, r26|->r7, r26|->r8, r26|->r9, r26|->r12, r26|->r15, r26|->r16, r26|->r17, r26|->r19, r26|->r20, r26|->r21, r26|->r22, r26|->r23, r26|->r24, r26|->r25, r27|->r1, r27|->r2, r27|->r4, r27|->r6, r27|->r7, r27|->r8, r27|->r9, r27|->r10, r27|->r11, r27|->r12, r27|->r13, r27|->r14, r27|->r15, r27|->r17, r27|->r20, r27|->r23, r27|->r25, r27|->r26, r28|->r4, r28|->r6, r28|->r7, r28|->r8, r28|->r10, r28|->r11, r28|->r12, r28|->r14, r28|->r16, r28|->r17, r28|->r20, r28|->r21, r28|->r22, r28|->r23, r28|->r24, r28|->r25, r28|->r27, r29|->r0, r29|->r1, r29|->r2, r29|->r5, r29|->r6, r29|->r8, r29|->r9, r29|->r10, r29|->r18, r29|->r19, r29|->r20, r29|->r24, r29|->r26, r29|->r27, r29|->r28, r30|->r0, r30|->r1, r30|->r2, r30|->r3, r30|->r5, r30|->r6, r30|->r9, r30|->r15, r30|->r16, r30|->r21, r30|->r22, r30|->r24, r30|->r25, r30|->r26, r31|->r2, r31|->r4, r31|->r8, r31|->r9, r31|->r10, r31|->r13, r31|->r15, r31|->r19, r31|->r24, r31|->r27, r31|->r28, r32|->r1, r32|->r6, r32|->r7, r32|->r8, r32|->r9, r32|->r10, r32|->r12, r32|->r13, r32|->r14, r32|->r22, r32|->r27, r32|->r29, r32|->r31, r33|->r0, r33|->r2, r33|->r4, r33|->r7, r33|->r10, r33|->r11, r33|->r13, r33|->r17, r33|->r19, r33|->r21, r33|->r23, r33|->r24, r33|->r25, r33|->r32, r34|->r0, r34|->r1, r34|->r2, r34|->r3, r34|->r4, r34|->r5, r34|->r6, r34|->r7, r34|->r8, r34|->r9, r34|->r11, r34|->r14, r34|->r15, r34|->r17, r34|->r18, r34|->r19, r34|->r22, r34|->r24, r34|->r25, r34|->r26, r34|->r27, r34|->r30, r34|->r31, r34|->r32} &
    rules={rule0|->(rec(su:s28,re:r15,mo:pro,pr: 2,co:{c4,c9,c8,c6,c5,c2,c7,c3,c0})), rule1|->(rec(su:s5,re:r26,mo:pro,pr: 1,co:{c4,c0,c1,c8,c9})), rule2|->(rec(su:s7,re:r19,mo:pro,pr: 3,co:{c1,c5,c0})), rule3|->(rec(su:s17,re:r22,mo:pro,pr: 2,co:{c2,c0,c3,c9})), rule4|->(rec(su:s24,re:r18,mo:per,pr: 0,co:{c7,c1})), rule5|->(rec(su:s21,re:r0,mo:pro,pr: 1,co:{c5,c7,c9,c4})), rule6|->(rec(su:s26,re:r30,mo:per,pr: 2,co:{c3,c2,c4,c1,c0,c9})), rule7|->(rec(su:s26,re:r24,mo:per,pr: 1,co:{c4,c3,c2,c1})), rule8|->(rec(su:s11,re:r31,mo:per,pr: 4,co:{c3,c8,c0,c7,c2})), rule9|->(rec(su:s1,re:r5,mo:pro,pr: 3,co:{c6,c3,c8,c4,c0,c9,c5})), rule10|->(rec(su:s24,re:r19,mo:pro,pr: 1,co:{c0,c3,c9,c6})), rule11|->(rec(su:s25,re:r0,mo:pro,pr: 0,co:{c4,c2})), rule12|->(rec(su:s9,re:r24,mo:per,pr: 2,co:{c4}))}

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