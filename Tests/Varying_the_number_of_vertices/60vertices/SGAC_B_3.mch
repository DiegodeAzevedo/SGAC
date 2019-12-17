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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29};
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
    e_sub={s2|->s0, s3|->s0, s3|->s2, s4|->s0, s4|->s2, s5|->s0, s5|->s1, s6|->s4, s6|->s5, s7|->s0, s7|->s2, s7|->s4, s7|->s5, s8|->s2, s8|->s6, s8|->s7, s9|->s0, s9|->s2, s9|->s3, s9|->s4, s9|->s6, s9|->s8, s10|->s0, s10|->s2, s10|->s3, s10|->s4, s10|->s5, s10|->s8, s11|->s1, s11|->s3, s11|->s6, s11|->s7, s11|->s9, s12|->s3, s12|->s4, s12|->s9, s12|->s10, s13|->s0, s13|->s1, s13|->s4, s13|->s5, s13|->s10, s14|->s1, s14|->s2, s14|->s4, s14|->s6, s14|->s7, s14|->s8, s14|->s9, s14|->s11, s15|->s2, s15|->s6, s15|->s7, s16|->s0, s16|->s1, s16|->s2, s16|->s4, s16|->s5, s16|->s6, s16|->s10, s16|->s12, s16|->s13, s17|->s0, s17|->s3, s17|->s5, s17|->s7, s17|->s9, s17|->s12, s17|->s13, s17|->s15, s18|->s0, s18|->s1, s18|->s6, s18|->s7, s18|->s8, s18|->s9, s18|->s10, s18|->s11, s18|->s12, s18|->s15, s18|->s17, s19|->s0, s19|->s2, s19|->s3, s19|->s8, s19|->s9, s19|->s12, s19|->s13, s19|->s18, s20|->s0, s20|->s1, s20|->s6, s20|->s8, s20|->s9, s20|->s11, s20|->s17, s20|->s18, s20|->s19, s21|->s1, s21|->s2, s21|->s3, s21|->s5, s21|->s7, s21|->s9, s21|->s11, s21|->s15, s21|->s18, s21|->s19, s22|->s0, s22|->s1, s22|->s3, s22|->s4, s22|->s5, s22|->s6, s22|->s7, s22|->s8, s22|->s13, s22|->s15, s22|->s16, s22|->s21, s23|->s0, s23|->s1, s23|->s4, s23|->s5, s23|->s7, s23|->s11, s23|->s14, s23|->s15, s23|->s16, s23|->s17, s23|->s18, s23|->s20, s23|->s22, s24|->s2, s24|->s5, s24|->s7, s24|->s9, s24|->s10, s24|->s11, s24|->s14, s24|->s19, s24|->s20, s24|->s21, s25|->s5, s25|->s6, s25|->s7, s25|->s8, s25|->s9, s25|->s10, s25|->s11, s25|->s14, s25|->s15, s25|->s16, s25|->s17, s25|->s18, s25|->s20, s25|->s21, s25|->s22, s25|->s23, s26|->s0, s26|->s7, s26|->s8, s26|->s9, s26|->s10, s26|->s12, s26|->s14, s26|->s16, s26|->s17, s26|->s19, s26|->s20, s26|->s24, s27|->s6, s27|->s7, s27|->s8, s27|->s9, s27|->s10, s27|->s11, s27|->s12, s27|->s14, s27|->s17, s27|->s20, s27|->s21, s27|->s22, s27|->s23, s27|->s24, s27|->s25, s28|->s0, s28|->s4, s28|->s14, s28|->s20, s28|->s24, s29|->s2, s29|->s4, s29|->s5, s29|->s9, s29|->s11, s29|->s13, s29|->s14, s29|->s15, s29|->s16, s29|->s17, s29|->s18, s29|->s19, s29|->s23, s29|->s25} &
    e_res={r3|->r1, r4|->r0, r4|->r1, r4|->r2, r4|->r3, r5|->r0, r5|->r1, r5|->r2, r5|->r3, r5|->r4, r6|->r2, r6|->r3, r6|->r4, r6|->r5, r7|->r0, r7|->r1, r7|->r2, r7|->r4, r7|->r5, r7|->r6, r8|->r0, r9|->r3, r9|->r5, r9|->r6, r9|->r7, r10|->r0, r10|->r2, r10|->r6, r10|->r9, r11|->r2, r11|->r3, r11|->r4, r11|->r6, r11|->r7, r11|->r8, r11|->r9, r11|->r10, r12|->r0, r12|->r2, r12|->r4, r12|->r5, r12|->r7, r12|->r8, r12|->r10, r13|->r3, r13|->r4, r13|->r6, r13|->r7, r13|->r8, r13|->r9, r13|->r10, r13|->r12, r14|->r0, r14|->r4, r14|->r5, r14|->r6, r14|->r8, r14|->r9, r14|->r12, r14|->r13, r15|->r1, r15|->r2, r15|->r5, r15|->r6, r15|->r7, r15|->r8, r15|->r9, r15|->r10, r15|->r11, r16|->r5, r16|->r6, r16|->r8, r16|->r9, r16|->r13, r16|->r14, r16|->r15, r17|->r0, r17|->r1, r17|->r3, r17|->r4, r17|->r5, r17|->r8, r17|->r9, r17|->r14, r17|->r16, r18|->r1, r18|->r2, r18|->r4, r18|->r5, r18|->r9, r18|->r10, r18|->r12, r18|->r13, r18|->r14, r19|->r0, r19|->r3, r19|->r4, r19|->r7, r19|->r10, r19|->r12, r20|->r0, r20|->r1, r20|->r2, r20|->r8, r20|->r11, r20|->r15, r20|->r16, r20|->r17, r20|->r19, r21|->r0, r21|->r1, r21|->r2, r21|->r3, r21|->r4, r21|->r5, r21|->r7, r21|->r8, r21|->r10, r21|->r12, r21|->r15, r21|->r17, r22|->r0, r22|->r1, r22|->r4, r22|->r7, r22|->r9, r22|->r10, r22|->r13, r22|->r14, r22|->r16, r22|->r17, r22|->r20, r22|->r21, r23|->r0, r23|->r1, r23|->r2, r23|->r3, r23|->r5, r23|->r7, r23|->r8, r23|->r11, r23|->r13, r23|->r17, r23|->r18, r23|->r19, r23|->r21, r23|->r22, r24|->r0, r24|->r2, r24|->r3, r24|->r4, r24|->r10, r24|->r13, r24|->r17, r24|->r22, r25|->r0, r25|->r1, r25|->r2, r25|->r4, r25|->r5, r25|->r6, r25|->r8, r25|->r13, r25|->r14, r25|->r15, r25|->r16, r25|->r17, r25|->r19, r25|->r20, r25|->r24, r26|->r0, r26|->r3, r26|->r4, r26|->r9, r26|->r12, r26|->r17, r26|->r19, r26|->r20, r26|->r23, r26|->r25, r27|->r0, r27|->r1, r27|->r2, r27|->r3, r27|->r4, r27|->r9, r27|->r11, r27|->r12, r27|->r15, r27|->r19, r27|->r20, r27|->r21, r27|->r22, r27|->r23, r27|->r25, r27|->r26, r28|->r2, r28|->r3, r28|->r7, r28|->r8, r28|->r11, r28|->r12, r28|->r13, r28|->r14, r28|->r17, r28|->r19, r28|->r20, r28|->r22, r28|->r27, r29|->r2, r29|->r3, r29|->r4, r29|->r5, r29|->r7, r29|->r9, r29|->r10, r29|->r11, r29|->r13, r29|->r14, r29|->r15, r29|->r16, r29|->r17, r29|->r18, r29|->r19, r29|->r20, r29|->r21, r29|->r23, r29|->r24, r29|->r26} &
    rules={rule0|->(rec(su:s14,re:r23,mo:per,pr: 4,co:{c1,c7,c2,c8})), rule1|->(rec(su:s22,re:r9,mo:pro,pr: 3,co:{c7,c1})), rule2|->(rec(su:s17,re:r4,mo:pro,pr: 0,co:{c4})), rule3|->(rec(su:s15,re:r22,mo:per,pr: 1,co:{c7,c4,c9,c2,c1,c5,c3})), rule4|->(rec(su:s23,re:r8,mo:per,pr: 0,co:{c0,c2,c8,c9})), rule5|->(rec(su:s1,re:r22,mo:per,pr: 0,co:{c4,c5,c6,c0,c9})), rule6|->(rec(su:s6,re:r9,mo:per,pr: 0,co:{c3})), rule7|->(rec(su:s19,re:r7,mo:pro,pr: 3,co:{c6,c8,c9,c4})), rule8|->(rec(su:s21,re:r13,mo:pro,pr: 0,co:{c1,c3,c5})), rule9|->(rec(su:s29,re:r8,mo:pro,pr: 3,co:{c5,c9})), rule10|->(rec(su:s0,re:r29,mo:pro,pr: 4,co:{c5})), rule11|->(rec(su:s0,re:r28,mo:per,pr: 2,co:{c6,c0,c1,c9,c2,c7,c5,c8})), rule12|->(rec(su:s22,re:r2,mo:pro,pr: 1,co:{c1,c5,c4,c8}))}

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