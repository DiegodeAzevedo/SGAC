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
    e_sub={s2|->s1, s3|->s2, s4|->s0, s4|->s1, s4|->s2, s5|->s3, s5|->s4, s6|->s3, s7|->s0, s7|->s1, s7|->s6, s8|->s1, s8|->s2, s8|->s3, s8|->s5, s8|->s6, s9|->s0, s9|->s4, s9|->s5, s10|->s1, s10|->s5, s10|->s6, s10|->s7, s10|->s8, s10|->s9, s11|->s2, s11|->s3, s11|->s5, s11|->s7, s11|->s8, s11|->s10, s12|->s2, s12|->s5, s12|->s10, s12|->s11, s13|->s0, s13|->s7, s13|->s8, s13|->s9, s13|->s11, s14|->s2, s14|->s5, s14|->s6, s14|->s9, s14|->s11, s14|->s13, s15|->s2, s15|->s3, s15|->s4, s15|->s6, s15|->s8, s15|->s11, s15|->s12, s15|->s13, s16|->s0, s16|->s1, s16|->s2, s16|->s3, s16|->s4, s16|->s5, s16|->s6, s16|->s9, s16|->s12, s16|->s13, s16|->s14, s16|->s15, s17|->s1, s17|->s5, s17|->s6, s17|->s9, s17|->s14, s17|->s15, s18|->s1, s18|->s4, s18|->s5, s18|->s6, s18|->s9, s18|->s10, s18|->s11, s18|->s13, s18|->s16, s19|->s0, s19|->s2, s19|->s3, s19|->s4, s19|->s5, s19|->s6, s19|->s7, s19|->s10, s19|->s14, s19|->s15, s19|->s17, s20|->s0, s20|->s1, s20|->s3, s20|->s4, s20|->s5, s20|->s8, s20|->s9, s20|->s13, s20|->s14, s20|->s15, s20|->s16, s20|->s19, s21|->s0, s21|->s2, s21|->s3, s21|->s4, s21|->s5, s21|->s7, s21|->s8, s21|->s10, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s15, s21|->s16, s21|->s17, s21|->s20, s22|->s0, s22|->s1, s22|->s4, s22|->s5, s22|->s8, s22|->s10, s22|->s11, s22|->s13, s22|->s14, s22|->s17, s22|->s18, s22|->s20, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s6, s23|->s7, s23|->s8, s23|->s9, s23|->s13, s23|->s17, s23|->s18, s23|->s19, s23|->s21, s23|->s22, s24|->s1, s24|->s3, s24|->s7, s24|->s11, s24|->s12, s24|->s14, s24|->s15, s24|->s18, s24|->s19, s24|->s21, s25|->s0, s25|->s3, s25|->s4, s25|->s5, s25|->s6, s25|->s7, s25|->s8, s25|->s9, s25|->s13, s25|->s17, s25|->s23, s26|->s1, s26|->s2, s26|->s4, s26|->s5, s26|->s9, s26|->s10, s26|->s11, s26|->s13, s26|->s16, s26|->s20, s26|->s22, s26|->s24, s27|->s0, s27|->s1, s27|->s2, s27|->s3, s27|->s4, s27|->s5, s27|->s6, s27|->s8, s27|->s9, s27|->s12, s27|->s13, s27|->s15, s27|->s24, s27|->s26, s28|->s1, s28|->s2, s28|->s3, s28|->s4, s28|->s6, s28|->s8, s28|->s9, s28|->s12, s28|->s14, s28|->s16, s28|->s17, s28|->s18, s28|->s19, s28|->s20, s28|->s21, s28|->s22, s28|->s23, s28|->s25, s29|->s0, s29|->s1, s29|->s4, s29|->s7, s29|->s8, s29|->s9, s29|->s10, s29|->s12, s29|->s14, s29|->s16, s29|->s18, s29|->s22, s29|->s25, s29|->s26, s30|->s0, s30|->s2, s30|->s5, s30|->s6, s30|->s7, s30|->s9, s30|->s10, s30|->s12, s30|->s14, s30|->s15, s30|->s20, s30|->s22, s30|->s25, s30|->s27, s31|->s1, s31|->s3, s31|->s4, s31|->s6, s31|->s8, s31|->s9, s31|->s10, s31|->s12, s31|->s13, s31|->s14, s31|->s15, s31|->s18, s31|->s19, s31|->s20, s31|->s24, s31|->s25, s31|->s26, s31|->s27, s31|->s28, s31|->s30, s32|->s0, s32|->s1, s32|->s2, s32|->s3, s32|->s4, s32|->s6, s32|->s9, s32|->s11, s32|->s13, s32|->s14, s32|->s15, s32|->s16, s32|->s17, s32|->s18, s32|->s20, s32|->s21, s32|->s24} &
    e_res={r1|->r0, r2|->r1, r3|->r1, r3|->r2, r4|->r0, r4|->r3, r5|->r0, r5|->r2, r5|->r3, r5|->r4, r6|->r0, r6|->r1, r6|->r3, r6|->r4, r6|->r5, r7|->r0, r7|->r4, r8|->r0, r8|->r1, r8|->r2, r8|->r3, r8|->r4, r8|->r5, r8|->r7, r9|->r3, r9|->r4, r10|->r2, r10|->r3, r10|->r4, r10|->r9, r11|->r0, r11|->r2, r11|->r4, r11|->r5, r11|->r6, r11|->r8, r11|->r9, r12|->r0, r12|->r3, r12|->r10, r12|->r11, r13|->r3, r13|->r4, r13|->r5, r13|->r8, r13|->r9, r14|->r0, r14|->r1, r14|->r2, r14|->r3, r14|->r6, r14|->r8, r14|->r10, r14|->r11, r14|->r12, r14|->r13, r15|->r4, r15|->r5, r15|->r7, r15|->r8, r15|->r10, r15|->r11, r15|->r12, r15|->r13, r16|->r3, r16|->r4, r16|->r5, r16|->r6, r16|->r9, r16|->r13, r16|->r14, r16|->r15, r17|->r1, r17|->r2, r17|->r3, r17|->r4, r17|->r5, r17|->r6, r17|->r8, r17|->r9, r17|->r12, r17|->r14, r17|->r16, r18|->r0, r18|->r2, r18|->r4, r18|->r5, r18|->r6, r18|->r7, r18|->r8, r18|->r10, r18|->r12, r18|->r14, r18|->r15, r18|->r16, r19|->r3, r19|->r4, r19|->r5, r19|->r6, r19|->r7, r19|->r9, r19|->r11, r19|->r13, r19|->r15, r19|->r17, r20|->r0, r20|->r1, r20|->r3, r20|->r4, r20|->r9, r20|->r10, r20|->r13, r20|->r16, r20|->r18, r20|->r19, r21|->r1, r21|->r2, r21|->r3, r21|->r4, r21|->r5, r21|->r8, r21|->r9, r21|->r10, r21|->r13, r21|->r15, r21|->r16, r21|->r17, r21|->r18, r21|->r19, r22|->r2, r22|->r4, r22|->r5, r22|->r7, r22|->r9, r22|->r13, r22|->r15, r22|->r17, r22|->r18, r22|->r19, r23|->r1, r23|->r2, r23|->r3, r23|->r6, r23|->r8, r23|->r9, r23|->r10, r23|->r12, r23|->r13, r23|->r18, r23|->r19, r23|->r20, r23|->r21, r23|->r22, r24|->r1, r24|->r4, r24|->r10, r24|->r16, r24|->r21, r24|->r22, r24|->r23, r25|->r0, r25|->r1, r25|->r4, r25|->r6, r25|->r8, r25|->r9, r25|->r17, r25|->r18, r25|->r19, r25|->r21, r26|->r2, r26|->r3, r26|->r6, r26|->r7, r26|->r8, r26|->r9, r26|->r11, r26|->r12, r26|->r16, r26|->r18, r26|->r19, r26|->r23, r27|->r2, r27|->r5, r27|->r6, r27|->r9, r27|->r11, r27|->r12, r27|->r14, r27|->r20, r27|->r23, r27|->r24, r27|->r25, r28|->r0, r28|->r3, r28|->r4, r28|->r11, r28|->r12, r28|->r14, r28|->r16, r28|->r17, r28|->r18, r28|->r19, r28|->r23, r28|->r27, r29|->r0, r29|->r1, r29|->r2, r29|->r3, r29|->r6, r29|->r8, r29|->r11, r29|->r19, r29|->r20, r29|->r21, r29|->r22, r29|->r24, r29|->r25, r30|->r0, r30|->r1, r30|->r2, r30|->r3, r30|->r4, r30|->r6, r30|->r7, r30|->r8, r30|->r9, r30|->r11, r30|->r14, r30|->r15, r30|->r17, r30|->r18, r30|->r23, r30|->r25, r31|->r0, r31|->r1, r31|->r3, r31|->r4, r31|->r5, r31|->r6, r31|->r7, r31|->r10, r31|->r11, r31|->r12, r31|->r16, r31|->r18, r31|->r19, r31|->r21, r31|->r22, r31|->r25, r31|->r27, r31|->r28} &
    rules={rule0|->(rec(su:s28,re:r4,mo:pro,pr: 3,co:{c1,c4})), rule1|->(rec(su:s18,re:r3,mo:per,pr: 0,co:{c6,c4,c2})), rule2|->(rec(su:s11,re:r19,mo:per,pr: 0,co:{c6,c0,c1,c3,c4})), rule3|->(rec(su:s8,re:r14,mo:pro,pr: 3,co:{c0,c1,c6,c7,c5})), rule4|->(rec(su:s12,re:r4,mo:pro,pr: 0,co:{c4})), rule5|->(rec(su:s18,re:r21,mo:per,pr: 0,co:{c9,c4,c1,c6,c8})), rule6|->(rec(su:s25,re:r16,mo:pro,pr: 4,co:{c8,c2,c7,c0})), rule7|->(rec(su:s14,re:r3,mo:per,pr: 1,co:{c4,c3,c7,c0,c8,c1,c5})), rule8|->(rec(su:s25,re:r31,mo:per,pr: 4,co:{c0,c3})), rule9|->(rec(su:s30,re:r5,mo:per,pr: 1,co:{c3,c6,c8,c7})), rule10|->(rec(su:s7,re:r18,mo:pro,pr: 4,co:{c1,c4,c3,c6,c0,c5,c2})), rule11|->(rec(su:s31,re:r15,mo:pro,pr: 2,co:{c5,c6,c7,c1,c9,c2,c8})), rule12|->(rec(su:s16,re:r20,mo:per,pr: 3,co:{c3,c4,c1,c8,c7,c9,c0}))}

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