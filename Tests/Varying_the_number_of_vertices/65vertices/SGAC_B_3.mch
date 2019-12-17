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
    e_sub={s1|->s0, s3|->s2, s4|->s0, s4|->s2, s4|->s3, s5|->s0, s5|->s3, s6|->s0, s6|->s1, s6|->s2, s6|->s5, s7|->s1, s7|->s3, s7|->s4, s8|->s1, s8|->s2, s8|->s3, s8|->s5, s8|->s7, s9|->s0, s9|->s1, s9|->s2, s9|->s3, s9|->s4, s9|->s5, s9|->s6, s9|->s8, s10|->s0, s10|->s2, s10|->s3, s10|->s4, s10|->s6, s10|->s7, s10|->s9, s11|->s1, s11|->s2, s11|->s3, s11|->s5, s11|->s6, s11|->s10, s12|->s0, s12|->s4, s12|->s5, s12|->s7, s12|->s8, s12|->s9, s12|->s10, s13|->s0, s13|->s3, s13|->s4, s13|->s5, s13|->s6, s13|->s9, s13|->s10, s13|->s12, s14|->s0, s14|->s1, s14|->s2, s14|->s3, s14|->s4, s14|->s5, s14|->s8, s14|->s13, s15|->s3, s15|->s6, s15|->s9, s15|->s10, s15|->s13, s15|->s14, s16|->s1, s16|->s2, s16|->s4, s16|->s8, s16|->s9, s16|->s10, s16|->s13, s16|->s15, s17|->s1, s17|->s3, s17|->s4, s17|->s5, s17|->s6, s17|->s14, s17|->s15, s18|->s3, s18|->s4, s18|->s6, s18|->s7, s18|->s8, s18|->s9, s18|->s10, s18|->s11, s18|->s13, s18|->s17, s19|->s2, s19|->s5, s19|->s7, s19|->s8, s19|->s12, s19|->s14, s19|->s16, s19|->s18, s20|->s1, s20|->s3, s20|->s7, s20|->s13, s20|->s14, s20|->s17, s21|->s2, s21|->s3, s21|->s7, s21|->s8, s21|->s9, s21|->s11, s21|->s13, s21|->s14, s21|->s17, s21|->s18, s21|->s20, s22|->s1, s22|->s3, s22|->s5, s22|->s6, s22|->s8, s22|->s9, s22|->s10, s22|->s12, s22|->s13, s22|->s14, s22|->s18, s22|->s20, s22|->s21, s23|->s0, s23|->s2, s23|->s4, s23|->s6, s23|->s10, s23|->s12, s23|->s15, s23|->s17, s23|->s18, s23|->s19, s23|->s20, s23|->s22, s24|->s1, s24|->s2, s24|->s4, s24|->s7, s24|->s8, s24|->s10, s24|->s11, s24|->s13, s24|->s14, s24|->s17, s24|->s18, s24|->s22, s25|->s0, s25|->s1, s25|->s7, s25|->s10, s25|->s11, s25|->s12, s25|->s13, s25|->s14, s25|->s18, s25|->s22, s25|->s24, s26|->s0, s26|->s2, s26|->s4, s26|->s5, s26|->s7, s26|->s8, s26|->s12, s26|->s15, s26|->s18, s26|->s20, s26|->s24, s26|->s25, s27|->s0, s27|->s1, s27|->s5, s27|->s8, s27|->s9, s27|->s11, s27|->s12, s27|->s14, s27|->s18, s27|->s20, s27|->s24, s27|->s25, s27|->s26, s28|->s4, s28|->s5, s28|->s6, s28|->s7, s28|->s9, s28|->s16, s28|->s18, s28|->s20, s28|->s21, s28|->s23, s28|->s25, s29|->s0, s29|->s1, s29|->s3, s29|->s4, s29|->s5, s29|->s9, s29|->s13, s29|->s14, s29|->s15, s29|->s16, s29|->s19, s29|->s20, s29|->s23, s29|->s25, s29|->s28, s30|->s0, s30|->s2, s30|->s3, s30|->s4, s30|->s5, s30|->s6, s30|->s7, s30|->s8, s30|->s10, s30|->s11, s30|->s13, s30|->s15, s30|->s18, s30|->s19, s30|->s20, s30|->s21, s30|->s22, s30|->s23, s30|->s24, s31|->s1, s31|->s3, s31|->s4, s31|->s6, s31|->s10, s31|->s11, s31|->s14, s31|->s16, s31|->s18, s31|->s20, s31|->s22, s31|->s26, s31|->s27, s31|->s28, s32|->s0, s32|->s1, s32|->s2, s32|->s4, s32|->s5, s32|->s6, s32|->s11, s32|->s13, s32|->s17, s32|->s18, s32|->s19, s32|->s20, s32|->s22, s32|->s23, s32|->s24, s32|->s27, s32|->s29, s32|->s30} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r3|->r1, r4|->r2, r5|->r0, r5|->r4, r6|->r0, r6|->r1, r6|->r3, r6|->r4, r7|->r0, r7|->r2, r8|->r2, r8|->r5, r8|->r6, r8|->r7, r9|->r0, r9|->r1, r9|->r3, r9|->r8, r10|->r0, r10|->r1, r10|->r2, r10|->r8, r11|->r1, r11|->r3, r11|->r5, r11|->r6, r11|->r8, r12|->r0, r12|->r2, r12|->r6, r12|->r8, r12|->r10, r13|->r3, r13|->r5, r13|->r6, r13|->r8, r14|->r0, r14|->r4, r14|->r5, r14|->r6, r14|->r7, r14|->r8, r14|->r11, r14|->r13, r15|->r0, r15|->r2, r15|->r3, r15|->r6, r15|->r9, r15|->r10, r15|->r11, r15|->r12, r16|->r0, r16|->r1, r16|->r3, r16|->r4, r16|->r5, r16|->r6, r16|->r7, r16|->r8, r16|->r11, r16|->r12, r16|->r13, r16|->r14, r16|->r15, r17|->r0, r17|->r6, r17|->r8, r17|->r9, r17|->r10, r17|->r11, r17|->r13, r17|->r14, r17|->r15, r17|->r16, r18|->r0, r18|->r1, r18|->r7, r18|->r8, r18|->r9, r18|->r10, r18|->r13, r18|->r16, r19|->r3, r19|->r5, r19|->r6, r19|->r7, r19|->r9, r19|->r10, r19|->r11, r19|->r12, r19|->r13, r19|->r15, r19|->r18, r20|->r0, r20|->r1, r20|->r2, r20|->r3, r20|->r4, r20|->r5, r20|->r8, r20|->r9, r20|->r10, r20|->r11, r20|->r12, r20|->r13, r20|->r14, r20|->r17, r21|->r2, r21|->r4, r21|->r6, r21|->r13, r21|->r19, r22|->r2, r22|->r3, r22|->r7, r22|->r10, r22|->r11, r22|->r12, r22|->r13, r22|->r14, r22|->r15, r22|->r18, r22|->r19, r23|->r0, r23|->r1, r23|->r11, r23|->r13, r23|->r15, r23|->r16, r23|->r17, r23|->r19, r23|->r20, r24|->r0, r24|->r1, r24|->r2, r24|->r4, r24|->r7, r24|->r8, r24|->r10, r24|->r11, r24|->r12, r24|->r13, r24|->r14, r24|->r15, r24|->r16, r24|->r17, r24|->r19, r24|->r20, r24|->r21, r24|->r22, r24|->r23, r25|->r1, r25|->r2, r25|->r5, r25|->r6, r25|->r8, r25|->r11, r25|->r13, r25|->r15, r25|->r18, r25|->r19, r25|->r20, r25|->r21, r25|->r22, r26|->r6, r26|->r10, r26|->r11, r26|->r12, r26|->r14, r26|->r20, r26|->r21, r26|->r22, r26|->r24, r27|->r0, r27|->r1, r27|->r4, r27|->r5, r27|->r9, r27|->r10, r27|->r11, r27|->r13, r27|->r16, r27|->r17, r27|->r20, r27|->r21, r27|->r22, r27|->r23, r27|->r24, r27|->r25, r28|->r0, r28|->r1, r28|->r3, r28|->r4, r28|->r5, r28|->r6, r28|->r7, r28|->r13, r28|->r15, r28|->r17, r28|->r19, r28|->r23, r28|->r24, r29|->r1, r29|->r6, r29|->r7, r29|->r8, r29|->r11, r29|->r16, r29|->r17, r29|->r21, r29|->r25, r29|->r27, r30|->r1, r30|->r2, r30|->r6, r30|->r7, r30|->r8, r30|->r10, r30|->r16, r30|->r18, r30|->r19, r30|->r22, r30|->r23, r31|->r1, r31|->r2, r31|->r3, r31|->r5, r31|->r6, r31|->r7, r31|->r9, r31|->r12, r31|->r14, r31|->r17, r31|->r22, r31|->r23, r31|->r24, r31|->r25, r31|->r27, r31|->r28, r31|->r29, r31|->r30} &
    rules={rule0|->(rec(su:s26,re:r13,mo:pro,pr: 2,co:{c8,c3,c4,c5})), rule1|->(rec(su:s19,re:r30,mo:pro,pr: 0,co:{c3,c4,c5,c9,c0,c8})), rule2|->(rec(su:s18,re:r17,mo:pro,pr: 1,co:{c1,c4,c5,c9,c8,c6})), rule3|->(rec(su:s13,re:r17,mo:pro,pr: 0,co:{c3,c5,c0,c8,c6,c7,c1})), rule4|->(rec(su:s28,re:r22,mo:pro,pr: 1,co:{c7,c1,c0})), rule5|->(rec(su:s20,re:r3,mo:per,pr: 0,co:{c4,c1})), rule6|->(rec(su:s15,re:r30,mo:pro,pr: 0,co:{c0,c4,c1,c6,c7,c3})), rule7|->(rec(su:s5,re:r28,mo:pro,pr: 3,co:{c1,c3})), rule8|->(rec(su:s4,re:r3,mo:per,pr: 3,co:{c1,c4,c2,c8,c7,c0,c5})), rule9|->(rec(su:s3,re:r18,mo:per,pr: 4,co:{c9,c8,c5,c1})), rule10|->(rec(su:s26,re:r24,mo:pro,pr: 1,co:{c3,c1,c4,c8,c9})), rule11|->(rec(su:s7,re:r22,mo:pro,pr: 4,co:{c1})), rule12|->(rec(su:s9,re:r3,mo:per,pr: 2,co:{c3}))}

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