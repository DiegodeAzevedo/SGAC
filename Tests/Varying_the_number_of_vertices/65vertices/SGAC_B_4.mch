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
    e_sub={s2|->s0, s2|->s1, s3|->s0, s3|->s1, s3|->s2, s4|->s1, s4|->s3, s5|->s0, s5|->s1, s5|->s2, s5|->s4, s6|->s0, s6|->s4, s6|->s5, s7|->s1, s7|->s3, s7|->s4, s8|->s0, s8|->s3, s8|->s6, s8|->s7, s9|->s1, s9|->s2, s9|->s3, s9|->s5, s9|->s7, s10|->s0, s10|->s3, s10|->s4, s10|->s9, s11|->s1, s11|->s3, s11|->s8, s11|->s9, s12|->s0, s12|->s4, s12|->s5, s12|->s7, s12|->s11, s13|->s0, s13|->s1, s13|->s3, s13|->s4, s13|->s6, s13|->s9, s13|->s11, s13|->s12, s14|->s0, s14|->s1, s14|->s3, s14|->s5, s14|->s6, s14|->s7, s14|->s9, s15|->s0, s15|->s3, s15|->s5, s15|->s10, s15|->s11, s16|->s0, s16|->s10, s16|->s14, s17|->s1, s17|->s2, s17|->s5, s17|->s7, s17|->s9, s17|->s10, s17|->s12, s17|->s14, s17|->s15, s17|->s16, s18|->s0, s18|->s1, s18|->s2, s18|->s8, s18|->s9, s18|->s12, s18|->s15, s18|->s16, s19|->s2, s19|->s3, s19|->s4, s19|->s5, s19|->s6, s19|->s7, s19|->s9, s19|->s10, s19|->s11, s19|->s12, s19|->s13, s19|->s14, s19|->s15, s19|->s16, s19|->s18, s20|->s2, s20|->s4, s20|->s5, s20|->s7, s20|->s11, s20|->s12, s20|->s13, s20|->s14, s20|->s16, s20|->s17, s21|->s2, s21|->s4, s21|->s7, s21|->s10, s21|->s12, s21|->s15, s21|->s17, s21|->s18, s22|->s0, s22|->s2, s22|->s3, s22|->s4, s22|->s9, s22|->s10, s22|->s11, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s19, s22|->s21, s23|->s0, s23|->s1, s23|->s7, s23|->s8, s23|->s11, s23|->s13, s23|->s15, s23|->s16, s23|->s17, s23|->s18, s23|->s21, s24|->s0, s24|->s1, s24|->s4, s24|->s5, s24|->s8, s24|->s9, s24|->s11, s24|->s15, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s20, s24|->s23, s25|->s2, s25|->s4, s25|->s5, s25|->s6, s25|->s7, s25|->s10, s25|->s11, s25|->s12, s25|->s13, s25|->s16, s25|->s18, s25|->s23, s25|->s24, s26|->s2, s26|->s8, s26|->s9, s26|->s12, s26|->s13, s26|->s16, s26|->s18, s26|->s20, s26|->s21, s26|->s22, s26|->s24, s26|->s25, s27|->s0, s27|->s1, s27|->s3, s27|->s8, s27|->s11, s27|->s13, s27|->s14, s27|->s15, s27|->s20, s27|->s21, s27|->s23, s27|->s25, s27|->s26, s28|->s1, s28|->s3, s28|->s4, s28|->s5, s28|->s6, s28|->s7, s28|->s8, s28|->s10, s28|->s12, s28|->s13, s28|->s14, s28|->s15, s28|->s17, s28|->s18, s28|->s20, s28|->s21, s28|->s22, s28|->s25, s28|->s27, s29|->s0, s29|->s4, s29|->s5, s29|->s6, s29|->s8, s29|->s9, s29|->s10, s29|->s11, s29|->s15, s29|->s17, s29|->s18, s29|->s19, s29|->s20, s29|->s23, s29|->s27, s29|->s28, s30|->s2, s30|->s4, s30|->s5, s30|->s6, s30|->s7, s30|->s8, s30|->s9, s30|->s10, s30|->s12, s30|->s18, s30|->s21, s30|->s22, s30|->s24, s30|->s25, s30|->s28, s31|->s0, s31|->s2, s31|->s3, s31|->s4, s31|->s8, s31|->s9, s31|->s10, s31|->s11, s31|->s12, s31|->s19, s31|->s20, s31|->s25, s31|->s26, s31|->s28, s31|->s30, s32|->s0, s32|->s2, s32|->s3, s32|->s5, s32|->s8, s32|->s10, s32|->s13, s32|->s16, s32|->s18, s32|->s19, s32|->s20, s32|->s21, s32|->s22, s32|->s25, s32|->s26, s32|->s29} &
    e_res={r4|->r2, r5|->r0, r5|->r3, r6|->r0, r6|->r3, r6|->r4, r6|->r5, r7|->r0, r7|->r1, r7|->r3, r7|->r5, r7|->r6, r8|->r0, r8|->r1, r8|->r2, r8|->r5, r9|->r2, r9|->r4, r9|->r5, r9|->r6, r9|->r7, r9|->r8, r10|->r1, r10|->r2, r10|->r6, r10|->r8, r11|->r2, r11|->r3, r11|->r4, r11|->r5, r11|->r7, r11|->r9, r12|->r0, r12|->r2, r12|->r3, r12|->r4, r12|->r7, r12|->r8, r12|->r9, r13|->r0, r13|->r5, r13|->r7, r13|->r9, r14|->r0, r14|->r4, r14|->r5, r14|->r6, r14|->r9, r14|->r10, r15|->r0, r15|->r1, r15|->r3, r15|->r4, r15|->r5, r15|->r6, r15|->r8, r15|->r9, r15|->r13, r15|->r14, r16|->r0, r16|->r3, r16|->r7, r16|->r8, r16|->r9, r16|->r10, r16|->r14, r16|->r15, r17|->r2, r17|->r4, r17|->r6, r17|->r8, r17|->r9, r17|->r11, r17|->r12, r17|->r15, r17|->r16, r18|->r0, r18|->r1, r18|->r2, r18|->r6, r18|->r10, r18|->r11, r18|->r14, r19|->r2, r19|->r5, r19|->r10, r19|->r12, r19|->r13, r19|->r15, r19|->r17, r19|->r18, r20|->r0, r20|->r3, r20|->r7, r20|->r10, r20|->r11, r20|->r13, r20|->r17, r20|->r18, r21|->r1, r21|->r4, r21|->r5, r21|->r9, r21|->r10, r21|->r14, r21|->r15, r21|->r19, r22|->r2, r22|->r3, r22|->r5, r22|->r7, r22|->r8, r22|->r9, r22|->r10, r22|->r12, r22|->r14, r22|->r16, r22|->r17, r22|->r18, r22|->r19, r22|->r21, r23|->r2, r23|->r6, r23|->r7, r23|->r8, r23|->r10, r23|->r13, r23|->r16, r23|->r18, r23|->r21, r24|->r0, r24|->r1, r24|->r2, r24|->r3, r24|->r5, r24|->r17, r24|->r18, r24|->r19, r24|->r20, r24|->r23, r25|->r1, r25|->r2, r25|->r3, r25|->r5, r25|->r8, r25|->r9, r25|->r11, r25|->r14, r25|->r16, r25|->r17, r25|->r18, r25|->r19, r25|->r23, r26|->r1, r26|->r5, r26|->r7, r26|->r11, r26|->r15, r26|->r16, r26|->r17, r26|->r18, r26|->r19, r26|->r22, r26|->r23, r26|->r25, r27|->r0, r27|->r1, r27|->r3, r27|->r4, r27|->r8, r27|->r9, r27|->r12, r27|->r17, r27|->r19, r27|->r21, r27|->r22, r27|->r24, r27|->r26, r28|->r0, r28|->r1, r28|->r7, r28|->r9, r28|->r10, r28|->r11, r28|->r14, r28|->r15, r28|->r16, r28|->r17, r28|->r19, r28|->r24, r29|->r1, r29|->r3, r29|->r4, r29|->r6, r29|->r9, r29|->r10, r29|->r11, r29|->r12, r29|->r13, r29|->r14, r29|->r15, r29|->r17, r29|->r20, r29|->r22, r29|->r23, r29|->r24, r29|->r26, r30|->r0, r30|->r1, r30|->r4, r30|->r8, r30|->r16, r30|->r17, r30|->r19, r30|->r20, r30|->r22, r30|->r24, r30|->r25, r31|->r2, r31|->r5, r31|->r11, r31|->r12, r31|->r18, r31|->r20, r31|->r22, r31|->r23, r31|->r25, r31|->r27, r31|->r28} &
    rules={rule0|->(rec(su:s14,re:r2,mo:per,pr: 3,co:{c8})), rule1|->(rec(su:s5,re:r5,mo:pro,pr: 3,co:{c6,c9,c7})), rule2|->(rec(su:s14,re:r23,mo:per,pr: 1,co:{c9,c5,c6,c1,c3})), rule3|->(rec(su:s3,re:r30,mo:pro,pr: 1,co:{c6,c2,c4,c9})), rule4|->(rec(su:s32,re:r9,mo:pro,pr: 0,co:{c6,c5,c9})), rule5|->(rec(su:s15,re:r20,mo:per,pr: 4,co:{c4,c0,c3,c5,c8,c2})), rule6|->(rec(su:s19,re:r2,mo:per,pr: 4,co:{c7,c1,c9,c3,c2,c4})), rule7|->(rec(su:s16,re:r20,mo:pro,pr: 4,co:{c0,c2,c9,c5})), rule8|->(rec(su:s16,re:r11,mo:pro,pr: 2,co:{c6})), rule9|->(rec(su:s5,re:r16,mo:per,pr: 0,co:{c4,c0,c1,c2,c3,c5,c6})), rule10|->(rec(su:s24,re:r15,mo:pro,pr: 3,co:{c7,c6,c2,c8})), rule11|->(rec(su:s28,re:r18,mo:pro,pr: 2,co:{c9,c6,c3,c1,c7,c5})), rule12|->(rec(su:s1,re:r28,mo:per,pr: 3,co:{c9,c3,c2,c8,c0,c5,c6}))}

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