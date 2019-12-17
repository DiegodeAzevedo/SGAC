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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31};
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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s5|->s0, s5|->s1, s5|->s3, s6|->s0, s6|->s2, s6|->s5, s7|->s0, s7|->s1, s7|->s4, s8|->s1, s8|->s2, s8|->s4, s8|->s7, s9|->s2, s9|->s6, s10|->s4, s10|->s6, s10|->s7, s10|->s9, s11|->s0, s11|->s2, s11|->s3, s11|->s4, s11|->s5, s11|->s6, s11|->s7, s11|->s8, s12|->s1, s12|->s2, s12|->s5, s12|->s6, s12|->s7, s13|->s3, s13|->s4, s13|->s5, s13|->s9, s13|->s10, s13|->s11, s13|->s12, s14|->s1, s14|->s2, s14|->s4, s14|->s10, s14|->s11, s15|->s1, s15|->s2, s15|->s3, s15|->s4, s15|->s5, s15|->s6, s15|->s7, s15|->s8, s15|->s14, s16|->s0, s16|->s1, s16|->s2, s16|->s4, s16|->s6, s16|->s7, s16|->s10, s16|->s11, s16|->s12, s16|->s14, s16|->s15, s17|->s5, s17|->s6, s17|->s8, s17|->s9, s17|->s10, s17|->s11, s17|->s12, s17|->s13, s17|->s14, s17|->s16, s18|->s0, s18|->s3, s18|->s4, s18|->s6, s18|->s8, s18|->s9, s18|->s11, s18|->s12, s18|->s13, s18|->s16, s19|->s0, s19|->s2, s19|->s3, s19|->s6, s19|->s7, s19|->s8, s19|->s11, s19|->s12, s19|->s15, s19|->s16, s20|->s1, s20|->s4, s20|->s5, s20|->s6, s20|->s7, s20|->s9, s20|->s10, s20|->s11, s20|->s12, s20|->s13, s20|->s14, s20|->s15, s20|->s17, s20|->s19, s21|->s0, s21|->s1, s21|->s3, s21|->s6, s21|->s7, s21|->s9, s21|->s10, s21|->s11, s21|->s18, s21|->s19, s21|->s20, s22|->s2, s22|->s5, s22|->s7, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s18, s22|->s20, s23|->s0, s23|->s3, s23|->s5, s23|->s6, s23|->s7, s23|->s8, s23|->s11, s23|->s13, s23|->s14, s23|->s17, s23|->s20, s23|->s22, s24|->s0, s24|->s2, s24|->s3, s24|->s4, s24|->s5, s24|->s6, s24|->s8, s24|->s9, s24|->s11, s24|->s12, s24|->s13, s24|->s14, s24|->s17, s24|->s18, s24|->s19, s24|->s20, s24|->s23, s25|->s0, s25|->s1, s25|->s5, s25|->s6, s25|->s8, s25|->s9, s25|->s14, s25|->s19, s25|->s20, s25|->s22, s25|->s23, s26|->s1, s26|->s3, s26|->s5, s26|->s6, s26|->s8, s26|->s10, s26|->s11, s26|->s17, s26|->s21, s26|->s22, s26|->s23, s26|->s24, s27|->s2, s27|->s3, s27|->s5, s27|->s6, s27|->s8, s27|->s11, s27|->s12, s27|->s13, s27|->s15, s27|->s16, s27|->s17, s27|->s18, s27|->s19, s27|->s20, s27|->s21, s27|->s26, s28|->s3, s28|->s7, s28|->s8, s28|->s13, s28|->s15, s28|->s17, s28|->s19, s28|->s21, s28|->s24, s28|->s25, s28|->s26, s28|->s27, s29|->s1, s29|->s2, s29|->s3, s29|->s4, s29|->s5, s29|->s7, s29|->s8, s29|->s11, s29|->s12, s29|->s14, s29|->s15, s29|->s17, s29|->s18, s29|->s21, s29|->s22, s29|->s25, s29|->s26, s30|->s2, s30|->s4, s30|->s5, s30|->s6, s30|->s10, s30|->s13, s30|->s14, s30|->s15, s30|->s20, s30|->s21, s30|->s25, s30|->s27, s30|->s28, s31|->s1, s31|->s3, s31|->s8, s31|->s9, s31|->s10, s31|->s14, s31|->s16, s31|->s17, s31|->s19, s31|->s20, s31|->s22, s31|->s23, s31|->s25, s31|->s27, s31|->s28, s31|->s29, s32|->s0, s32|->s2, s32|->s4, s32|->s6, s32|->s8, s32|->s13, s32|->s15, s32|->s16, s32|->s17, s32|->s21, s32|->s22, s32|->s24, s32|->s31} &
    e_res={r3|->r0, r3|->r1, r4|->r0, r4|->r1, r4|->r2, r4|->r3, r5|->r1, r5|->r3, r5|->r4, r6|->r4, r7|->r2, r7|->r6, r8|->r0, r8|->r4, r8|->r7, r9|->r1, r9|->r2, r9|->r3, r9|->r7, r10|->r0, r10|->r1, r10|->r3, r10|->r4, r10|->r5, r10|->r6, r10|->r8, r11|->r5, r11|->r6, r11|->r8, r11|->r10, r12|->r2, r12|->r5, r12|->r7, r12|->r8, r13|->r1, r13|->r2, r13|->r5, r13|->r12, r14|->r0, r14|->r2, r14|->r3, r14|->r5, r14|->r6, r14|->r7, r14|->r8, r14|->r10, r14|->r11, r15|->r1, r15|->r4, r15|->r7, r15|->r8, r15|->r9, r15|->r10, r15|->r11, r15|->r12, r15|->r14, r16|->r0, r16|->r1, r16|->r3, r16|->r4, r16|->r11, r16|->r12, r16|->r15, r17|->r2, r17|->r5, r17|->r7, r17|->r8, r17|->r9, r17|->r11, r17|->r12, r17|->r13, r17|->r14, r17|->r15, r18|->r0, r18|->r1, r18|->r2, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r7, r18|->r8, r18|->r10, r18|->r11, r18|->r14, r19|->r1, r19|->r2, r19|->r3, r19|->r5, r19|->r6, r19|->r10, r19|->r17, r20|->r0, r20|->r1, r20|->r2, r20|->r8, r20|->r9, r20|->r10, r20|->r11, r20|->r12, r20|->r13, r20|->r14, r20|->r18, r21|->r0, r21|->r1, r21|->r2, r21|->r5, r21|->r9, r21|->r10, r21|->r11, r21|->r12, r21|->r15, r21|->r16, r21|->r19, r22|->r0, r22|->r2, r22|->r4, r22|->r6, r22|->r7, r22|->r8, r22|->r9, r22|->r10, r22|->r14, r22|->r17, r22|->r19, r23|->r0, r23|->r6, r23|->r7, r23|->r8, r23|->r9, r23|->r10, r23|->r13, r23|->r15, r23|->r16, r23|->r18, r23|->r19, r23|->r20, r23|->r21, r23|->r22, r24|->r0, r24|->r2, r24|->r5, r24|->r8, r24|->r9, r24|->r10, r24|->r12, r24|->r13, r24|->r16, r24|->r17, r24|->r19, r24|->r22, r24|->r23, r25|->r0, r25|->r2, r25|->r4, r25|->r5, r25|->r9, r25|->r10, r25|->r11, r25|->r15, r25|->r21, r25|->r24, r26|->r1, r26|->r4, r26|->r5, r26|->r6, r26|->r8, r26|->r9, r26|->r10, r26|->r11, r26|->r15, r26|->r18, r26|->r19, r26|->r20, r26|->r22, r26|->r23, r27|->r0, r27|->r4, r27|->r7, r27|->r9, r27|->r10, r27|->r14, r27|->r15, r27|->r16, r27|->r17, r27|->r19, r27|->r22, r27|->r23, r27|->r24, r27|->r26, r28|->r1, r28|->r3, r28|->r7, r28|->r9, r28|->r10, r28|->r15, r28|->r19, r28|->r22, r28|->r23, r29|->r1, r29|->r2, r29|->r3, r29|->r4, r29|->r5, r29|->r6, r29|->r7, r29|->r8, r29|->r9, r29|->r10, r29|->r11, r29|->r12, r29|->r13, r29|->r16, r29|->r17, r29|->r18, r29|->r19, r29|->r20, r29|->r22, r29|->r24, r30|->r0, r30|->r4, r30|->r6, r30|->r10, r30|->r13, r30|->r14, r30|->r15, r30|->r17, r30|->r20, r30|->r21, r30|->r24, r30|->r27, r30|->r28, r31|->r0, r31|->r1, r31|->r6, r31|->r9, r31|->r10, r31|->r11, r31|->r12, r31|->r14, r31|->r17, r31|->r19, r31|->r21, r31|->r22, r31|->r23, r31|->r25, r31|->r30} &
    rules={rule0|->(rec(su:s3,re:r11,mo:per,pr: 3,co:{c7,c5,c8,c9,c4,c3,c6})), rule1|->(rec(su:s0,re:r14,mo:pro,pr: 4,co:{c9,c5,c7,c6,c8})), rule2|->(rec(su:s4,re:r17,mo:per,pr: 0,co:{c0,c1,c6,c3,c2})), rule3|->(rec(su:s25,re:r31,mo:pro,pr: 0,co:{c6,c8,c0,c3,c5,c9})), rule4|->(rec(su:s22,re:r0,mo:pro,pr: 0,co:{c7,c2,c8,c6})), rule5|->(rec(su:s15,re:r29,mo:pro,pr: 4,co:{c7,c3,c2,c4,c0,c1})), rule6|->(rec(su:s3,re:r23,mo:per,pr: 2,co:{c3,c5,c7})), rule7|->(rec(su:s22,re:r26,mo:per,pr: 2,co:{c6,c1,c8,c4,c0,c7})), rule8|->(rec(su:s6,re:r24,mo:pro,pr: 3,co:{c4,c1,c7})), rule9|->(rec(su:s15,re:r26,mo:per,pr: 3,co:{c6,c4,c3})), rule10|->(rec(su:s32,re:r16,mo:pro,pr: 0,co:{c1,c5})), rule11|->(rec(su:s17,re:r23,mo:per,pr: 0,co:{c6,c2,c1,c9,c4,c8})), rule12|->(rec(su:s23,re:r19,mo:per,pr: 3,co:{c9}))}

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