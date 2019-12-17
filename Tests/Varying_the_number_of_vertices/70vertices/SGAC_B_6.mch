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
    e_sub={s2|->s0, s2|->s1, s3|->s0, s3|->s1, s4|->s0, s4|->s1, s5|->s1, s5|->s4, s6|->s0, s6|->s1, s6|->s4, s7|->s0, s7|->s2, s7|->s3, s7|->s4, s8|->s2, s8|->s4, s9|->s2, s9|->s4, s10|->s3, s10|->s4, s10|->s7, s10|->s9, s11|->s0, s11|->s5, s11|->s6, s11|->s7, s11|->s8, s11|->s9, s12|->s1, s12|->s2, s12|->s6, s12|->s8, s12|->s9, s12|->s10, s12|->s11, s13|->s1, s13|->s2, s13|->s3, s13|->s4, s13|->s7, s13|->s8, s13|->s12, s14|->s2, s14|->s3, s14|->s4, s14|->s6, s14|->s9, s14|->s10, s14|->s13, s15|->s0, s15|->s1, s15|->s2, s15|->s4, s15|->s7, s15|->s8, s15|->s9, s16|->s0, s16|->s1, s16|->s2, s16|->s3, s16|->s4, s16|->s6, s16|->s10, s16|->s12, s16|->s15, s17|->s4, s17|->s7, s17|->s8, s17|->s10, s17|->s11, s17|->s15, s18|->s0, s18|->s1, s18|->s3, s18|->s4, s18|->s9, s18|->s10, s18|->s11, s18|->s13, s18|->s14, s18|->s16, s18|->s17, s19|->s1, s19|->s7, s19|->s13, s19|->s14, s19|->s16, s19|->s18, s20|->s0, s20|->s7, s20|->s10, s20|->s11, s20|->s18, s20|->s19, s21|->s2, s21|->s3, s21|->s4, s21|->s6, s21|->s7, s21|->s8, s21|->s11, s21|->s14, s21|->s15, s21|->s16, s21|->s17, s21|->s18, s21|->s19, s22|->s1, s22|->s2, s22|->s3, s22|->s8, s22|->s11, s22|->s12, s22|->s14, s22|->s15, s22|->s17, s22|->s19, s22|->s20, s23|->s0, s23|->s2, s23|->s6, s23|->s7, s23|->s12, s23|->s13, s23|->s14, s23|->s15, s23|->s19, s23|->s22, s24|->s3, s24|->s5, s24|->s7, s24|->s9, s24|->s11, s24|->s13, s24|->s15, s24|->s16, s24|->s17, s24|->s20, s24|->s21, s24|->s22, s24|->s23, s25|->s2, s25|->s3, s25|->s8, s25|->s9, s25|->s12, s25|->s13, s25|->s14, s25|->s15, s25|->s23, s25|->s24, s26|->s2, s26|->s4, s26|->s8, s26|->s9, s26|->s10, s26|->s11, s26|->s12, s26|->s18, s26|->s21, s26|->s22, s26|->s23, s27|->s1, s27|->s3, s27|->s4, s27|->s5, s27|->s7, s27|->s9, s27|->s10, s27|->s15, s27|->s16, s27|->s21, s27|->s23, s27|->s24, s27|->s25, s28|->s1, s28|->s4, s28|->s5, s28|->s6, s28|->s9, s28|->s11, s28|->s13, s28|->s19, s28|->s24, s28|->s26, s29|->s0, s29|->s2, s29|->s3, s29|->s6, s29|->s7, s29|->s8, s29|->s9, s29|->s11, s29|->s12, s29|->s13, s29|->s15, s29|->s18, s29|->s19, s29|->s24, s29|->s25, s29|->s28, s30|->s2, s30|->s6, s30|->s7, s30|->s8, s30|->s9, s30|->s10, s30|->s13, s30|->s15, s30|->s22, s30|->s23, s30|->s26, s30|->s27, s31|->s0, s31|->s3, s31|->s6, s31|->s7, s31|->s8, s31|->s9, s31|->s12, s31|->s13, s31|->s16, s31|->s18, s31|->s21, s31|->s23, s31|->s24, s31|->s26, s31|->s30, s32|->s0, s32|->s3, s32|->s4, s32|->s5, s32|->s8, s32|->s9, s32|->s10, s32|->s11, s32|->s14, s32|->s15, s32|->s17, s32|->s18, s32|->s21, s32|->s22, s32|->s23, s32|->s24, s33|->s0, s33|->s1, s33|->s2, s33|->s4, s33|->s8, s33|->s11, s33|->s17, s33|->s18, s33|->s21, s33|->s22, s33|->s25, s33|->s26, s33|->s28, s33|->s30, s33|->s31, s34|->s1, s34|->s2, s34|->s3, s34|->s4, s34|->s5, s34|->s9, s34|->s12, s34|->s13, s34|->s15, s34|->s16, s34|->s17, s34|->s22, s34|->s23, s34|->s24, s34|->s26, s34|->s27, s34|->s31, s34|->s32, s34|->s33} &
    e_res={r3|->r0, r3|->r1, r3|->r2, r4|->r0, r4|->r1, r4|->r3, r5|->r0, r5|->r3, r7|->r1, r7|->r2, r7|->r3, r8|->r1, r8|->r4, r8|->r5, r8|->r6, r8|->r7, r9|->r1, r9|->r2, r9|->r3, r9|->r4, r9|->r6, r9|->r7, r10|->r5, r10|->r6, r10|->r7, r10|->r8, r11|->r0, r11|->r2, r11|->r3, r11|->r4, r11|->r5, r11|->r6, r11|->r7, r11|->r9, r11|->r10, r12|->r4, r12|->r5, r13|->r0, r13|->r1, r13|->r3, r13|->r5, r13|->r6, r13|->r8, r13|->r9, r13|->r11, r13|->r12, r14|->r5, r14|->r6, r14|->r7, r14|->r8, r14|->r11, r14|->r12, r14|->r13, r15|->r0, r15|->r1, r15|->r4, r15|->r5, r15|->r9, r15|->r10, r15|->r11, r16|->r2, r16|->r3, r16|->r4, r16|->r9, r16|->r10, r16|->r12, r17|->r0, r17|->r2, r17|->r10, r17|->r12, r17|->r13, r17|->r15, r17|->r16, r18|->r0, r18|->r1, r18|->r3, r18|->r5, r18|->r6, r18|->r7, r18|->r8, r18|->r9, r18|->r10, r18|->r12, r18|->r14, r18|->r15, r19|->r5, r19|->r10, r19|->r12, r19|->r14, r19|->r15, r19|->r16, r19|->r18, r20|->r0, r20|->r1, r20|->r2, r20|->r5, r20|->r6, r20|->r7, r20|->r8, r20|->r9, r20|->r10, r20|->r11, r20|->r12, r20|->r14, r20|->r15, r20|->r16, r20|->r18, r20|->r19, r21|->r0, r21|->r2, r21|->r3, r21|->r8, r21|->r9, r21|->r10, r21|->r11, r21|->r12, r21|->r13, r21|->r14, r21|->r16, r21|->r17, r22|->r0, r22|->r1, r22|->r2, r22|->r6, r22|->r8, r22|->r9, r22|->r10, r22|->r11, r22|->r13, r22|->r14, r22|->r15, r22|->r17, r22|->r18, r23|->r5, r23|->r6, r23|->r9, r23|->r14, r23|->r17, r23|->r18, r23|->r20, r23|->r22, r24|->r0, r24|->r2, r24|->r3, r24|->r5, r24|->r6, r24|->r7, r24|->r8, r24|->r9, r24|->r12, r24|->r15, r24|->r17, r24|->r18, r24|->r20, r24|->r22, r24|->r23, r25|->r0, r25|->r3, r25|->r4, r25|->r5, r25|->r6, r25|->r10, r25|->r11, r25|->r12, r25|->r13, r25|->r14, r25|->r15, r25|->r18, r25|->r19, r25|->r21, r25|->r22, r26|->r1, r26|->r2, r26|->r4, r26|->r5, r26|->r8, r26|->r10, r26|->r12, r26|->r14, r26|->r16, r26|->r17, r26|->r18, r26|->r20, r26|->r21, r26|->r24, r26|->r25, r27|->r2, r27|->r3, r27|->r4, r27|->r5, r27|->r7, r27|->r8, r27|->r11, r27|->r12, r27|->r13, r27|->r14, r27|->r15, r27|->r16, r27|->r17, r27|->r18, r27|->r19, r27|->r20, r27|->r22, r27|->r23, r27|->r25, r27|->r26, r28|->r1, r28|->r3, r28|->r5, r28|->r11, r28|->r19, r28|->r20, r28|->r23, r28|->r25, r29|->r0, r29|->r3, r29|->r8, r29|->r11, r29|->r13, r29|->r16, r29|->r17, r29|->r18, r29|->r19, r29|->r20, r29|->r21, r29|->r23, r29|->r25, r29|->r27, r30|->r2, r30|->r3, r30|->r4, r30|->r8, r30|->r9, r30|->r11, r30|->r14, r30|->r15, r30|->r16, r30|->r18, r30|->r19, r30|->r22, r30|->r24, r30|->r28, r30|->r29, r31|->r6, r31|->r11, r31|->r12, r31|->r13, r31|->r16, r31|->r17, r31|->r18, r31|->r19, r31|->r23, r31|->r24, r31|->r26, r31|->r27, r31|->r30, r32|->r1, r32|->r4, r32|->r5, r32|->r7, r32|->r8, r32|->r9, r32|->r10, r32|->r12, r32|->r15, r32|->r17, r32|->r18, r32|->r19, r32|->r20, r32|->r21, r32|->r23, r32|->r24, r32|->r27, r32|->r31, r33|->r1, r33|->r2, r33|->r3, r33|->r4, r33|->r8, r33|->r10, r33|->r11, r33|->r12, r33|->r14, r33|->r16, r33|->r17, r33|->r18, r33|->r19, r33|->r21, r33|->r24, r33|->r27, r33|->r30, r33|->r32, r34|->r0, r34|->r3, r34|->r4, r34|->r7, r34|->r8, r34|->r9, r34|->r11, r34|->r12, r34|->r13, r34|->r14, r34|->r15, r34|->r18, r34|->r21, r34|->r23, r34|->r25, r34|->r26, r34|->r30, r34|->r32, r34|->r33} &
    rules={rule0|->(rec(su:s30,re:r5,mo:pro,pr: 4,co:{c3,c4})), rule1|->(rec(su:s23,re:r13,mo:pro,pr: 3,co:{c2})), rule2|->(rec(su:s34,re:r12,mo:pro,pr: 3,co:{c8,c1})), rule3|->(rec(su:s34,re:r5,mo:pro,pr: 2,co:{c5,c0,c3,c2})), rule4|->(rec(su:s11,re:r10,mo:pro,pr: 2,co:{c0,c8})), rule5|->(rec(su:s34,re:r33,mo:pro,pr: 4,co:{c1,c0,c9,c2,c5})), rule6|->(rec(su:s21,re:r25,mo:pro,pr: 1,co:{c1,c2,c7,c9,c0,c8,c3,c5})), rule7|->(rec(su:s13,re:r31,mo:pro,pr: 1,co:{c2,c7,c5,c6,c0,c8,c9,c3,c1})), rule8|->(rec(su:s32,re:r6,mo:per,pr: 1,co:{c3,c6,c1,c8})), rule9|->(rec(su:s2,re:r23,mo:per,pr: 4,co:{c6})), rule10|->(rec(su:s2,re:r20,mo:per,pr: 4,co:{c1,c0,c9})), rule11|->(rec(su:s0,re:r1,mo:per,pr: 4,co:{c1,c0,c3,c6,c5})), rule12|->(rec(su:s20,re:r29,mo:per,pr: 1,co:{c5,c8,c6,c7,c4}))}

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