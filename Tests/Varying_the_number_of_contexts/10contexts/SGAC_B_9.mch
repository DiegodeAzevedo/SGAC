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
    RULE_T={rule0, rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8, rule9, rule10, rule11};
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
    e_sub={s2|->s1, s3|->s0, s3|->s1, s5|->s0, s5|->s1, s5|->s2, s5|->s4, s6|->s0, s6|->s1, s6|->s2, s6|->s5, s7|->s1, s7|->s2, s7|->s4, s7|->s6, s8|->s3, s9|->s0, s9|->s1, s9|->s7, s10|->s1, s10|->s3, s10|->s4, s10|->s8, s11|->s1, s11|->s3, s11|->s4, s11|->s6, s11|->s7, s11|->s9, s12|->s0, s12|->s1, s12|->s5, s12|->s7, s12|->s10, s12|->s11, s13|->s0, s13|->s2, s13|->s3, s13|->s6, s13|->s7, s13|->s9, s13|->s10, s13|->s11, s14|->s0, s14|->s2, s14|->s8, s14|->s10, s14|->s12, s15|->s1, s15|->s2, s15|->s4, s15|->s8, s15|->s9, s15|->s11, s16|->s0, s16|->s1, s16|->s2, s16|->s4, s16|->s9, s16|->s11, s16|->s13, s16|->s14, s17|->s2, s17|->s3, s17|->s4, s17|->s6, s17|->s9, s17|->s10, s17|->s13, s17|->s14, s17|->s16, s18|->s1, s18|->s3, s18|->s4, s18|->s5, s18|->s7, s18|->s8, s18|->s9, s18|->s10, s18|->s12, s18|->s13, s18|->s15, s18|->s17, s19|->s0, s19|->s2, s19|->s3, s19|->s4, s19|->s6, s19|->s7, s19|->s8, s19|->s11, s19|->s15, s19|->s18, s20|->s0, s20|->s1, s20|->s2, s20|->s5, s20|->s7, s20|->s8, s20|->s9, s20|->s11, s20|->s15, s20|->s16, s20|->s17, s20|->s18, s20|->s19, s21|->s3, s21|->s4, s21|->s5, s21|->s6, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s18, s22|->s0, s22|->s4, s22|->s7, s22|->s8, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s17, s22|->s19, s22|->s20, s23|->s0, s23|->s1, s23|->s2, s23|->s4, s23|->s5, s23|->s6, s23|->s7, s23|->s8, s23|->s11, s23|->s13, s23|->s14, s23|->s17, s23|->s18, s23|->s19, s23|->s21, s23|->s22, s24|->s1, s24|->s2, s24|->s3, s24|->s4, s24|->s5, s24|->s6, s24|->s9, s24|->s12, s24|->s16, s24|->s19, s24|->s23, s25|->s0, s25|->s1, s25|->s3, s25|->s6, s25|->s9, s25|->s10, s25|->s12, s25|->s14, s25|->s15, s25|->s18, s25|->s20, s25|->s21, s25|->s23, s25|->s24, s26|->s0, s26|->s3, s26|->s6, s26|->s13, s26|->s15, s26|->s16, s26|->s19, s26|->s23, s26|->s25, s27|->s0, s27|->s2, s27|->s6, s27|->s7, s27|->s8, s27|->s9, s27|->s11, s27|->s16, s27|->s17, s27|->s18, s27|->s20, s27|->s21, s27|->s22, s27|->s24, s27|->s25, s27|->s26, s28|->s1, s28|->s2, s28|->s6, s28|->s7, s28|->s10, s28|->s12, s28|->s13, s28|->s14, s28|->s18, s28|->s23, s28|->s25, s28|->s26, s28|->s27, s29|->s1, s29|->s3, s29|->s7, s29|->s8, s29|->s12, s29|->s14, s29|->s17, s29|->s19, s29|->s22, s29|->s23, s29|->s24, s29|->s25, s29|->s26, s29|->s27} &
    e_res={r2|->r1, r4|->r3, r5|->r3, r6|->r1, r6|->r5, r7|->r1, r7|->r2, r7|->r6, r8|->r1, r8|->r3, r8|->r5, r8|->r6, r9|->r0, r9|->r6, r9|->r8, r10|->r1, r10|->r3, r10|->r5, r10|->r6, r10|->r8, r11|->r0, r11|->r1, r11|->r2, r11|->r3, r11|->r4, r11|->r5, r11|->r6, r11|->r8, r12|->r0, r12|->r3, r12|->r8, r12|->r10, r12|->r11, r13|->r0, r13|->r3, r13|->r5, r13|->r7, r13|->r8, r13|->r9, r13|->r11, r13|->r12, r14|->r3, r14|->r7, r14|->r9, r15|->r3, r15|->r6, r15|->r9, r15|->r10, r15|->r14, r16|->r0, r16|->r3, r16|->r4, r16|->r6, r16|->r9, r16|->r10, r16|->r13, r17|->r1, r17|->r3, r17|->r4, r17|->r5, r17|->r6, r17|->r7, r17|->r9, r17|->r14, r17|->r15, r17|->r16, r18|->r2, r18|->r3, r18|->r5, r18|->r9, r18|->r13, r18|->r14, r18|->r16, r19|->r3, r19|->r6, r19|->r8, r19|->r11, r19|->r12, r19|->r13, r19|->r16, r19|->r17, r19|->r18, r20|->r0, r20|->r1, r20|->r3, r20|->r6, r20|->r8, r20|->r9, r20|->r11, r20|->r12, r20|->r13, r20|->r14, r20|->r16, r20|->r17, r20|->r19, r21|->r1, r21|->r5, r21|->r6, r21|->r8, r21|->r9, r21|->r10, r21|->r13, r21|->r14, r21|->r15, r21|->r16, r21|->r19, r22|->r4, r22|->r5, r22|->r6, r22|->r7, r22|->r8, r22|->r9, r22|->r12, r22|->r13, r22|->r14, r22|->r15, r22|->r20, r23|->r4, r23|->r8, r23|->r9, r23|->r10, r23|->r11, r23|->r12, r23|->r13, r23|->r14, r23|->r15, r23|->r16, r23|->r20, r23|->r21, r24|->r4, r24|->r5, r24|->r6, r24|->r7, r24|->r8, r24|->r10, r24|->r11, r24|->r18, r24|->r20, r24|->r21, r24|->r22, r25|->r0, r25|->r2, r25|->r5, r25|->r6, r25|->r7, r25|->r10, r25|->r11, r25|->r12, r25|->r15, r25|->r19, r25|->r20, r25|->r22, r26|->r2, r26|->r3, r26|->r8, r26|->r10, r26|->r14, r26|->r16, r26|->r21, r26|->r24, r26|->r25, r27|->r0, r27|->r1, r27|->r5, r27|->r6, r27|->r10, r27|->r11, r27|->r13, r27|->r14, r27|->r15, r27|->r18, r27|->r20, r27|->r22, r27|->r24, r27|->r25, r28|->r0, r28|->r1, r28|->r4, r28|->r5, r28|->r6, r28|->r7, r28|->r9, r28|->r10, r28|->r15, r28|->r16, r28|->r18, r28|->r22, r28|->r23, r28|->r26, r28|->r27, r29|->r1, r29|->r2, r29|->r3, r29|->r12, r29|->r17, r29|->r19, r29|->r23, r29|->r25, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s11,re:r8,mo:pro,pr: 4,co:{c5,c7,c9})), rule1|->(rec(su:s3,re:r10,mo:per,pr: 2,co:{c6,c7,c9,c2})), rule2|->(rec(su:s4,re:r4,mo:pro,pr: 2,co:{c6,c4,c1,c0,c2,c3})), rule3|->(rec(su:s22,re:r14,mo:per,pr: 4,co:{c6,c0,c3,c9,c2})), rule4|->(rec(su:s24,re:r8,mo:pro,pr: 2,co:{c6,c9,c8,c4})), rule5|->(rec(su:s16,re:r16,mo:per,pr: 4,co:{c0,c1,c2})), rule6|->(rec(su:s19,re:r0,mo:pro,pr: 1,co:{c9,c5,c8,c6,c3,c0,c4})), rule7|->(rec(su:s27,re:r6,mo:pro,pr: 3,co:{c3,c6,c0,c1,c5})), rule8|->(rec(su:s4,re:r13,mo:pro,pr: 0,co:{c2,c1,c8,c3})), rule9|->(rec(su:s0,re:r6,mo:pro,pr: 4,co:{c7,c9,c2,c0,c4})), rule10|->(rec(su:s21,re:r26,mo:per,pr: 2,co:{c6})), rule11|->(rec(su:s13,re:r17,mo:per,pr: 4,co:{c4,c1,c9}))}

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