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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s3|->s1, s4|->s0, s4|->s1, s4|->s3, s5|->s1, s5|->s2, s6|->s2, s6|->s3, s6|->s4, s6|->s5, s7|->s0, s7|->s2, s7|->s4, s7|->s6, s8|->s4, s8|->s7, s9|->s3, s9|->s4, s9|->s5, s9|->s7, s9|->s8, s10|->s0, s10|->s2, s10|->s5, s11|->s3, s11|->s4, s11|->s7, s11|->s8, s11|->s10, s12|->s10, s13|->s0, s13|->s2, s13|->s4, s13|->s5, s13|->s11, s13|->s12, s14|->s5, s15|->s1, s15|->s3, s15|->s5, s15|->s6, s15|->s7, s15|->s9, s15|->s10, s15|->s12, s15|->s13, s16|->s1, s16|->s2, s16|->s3, s16|->s4, s16|->s6, s16|->s7, s16|->s11, s16|->s12, s16|->s14, s17|->s0, s17|->s1, s17|->s5, s17|->s6, s17|->s7, s17|->s10, s17|->s11, s17|->s12, s17|->s13, s17|->s14, s17|->s16, s18|->s0, s18|->s1, s18|->s2, s18|->s4, s18|->s6, s18|->s7, s18|->s10, s18|->s11, s18|->s12, s18|->s13, s18|->s15, s18|->s17, s19|->s0, s19|->s1, s19|->s2, s19|->s4, s19|->s8, s19|->s9, s19|->s10, s19|->s15, s19|->s18, s20|->s0, s20|->s1, s20|->s3, s20|->s4, s20|->s10, s20|->s12, s20|->s13, s20|->s16, s20|->s18, s21|->s1, s21|->s2, s21|->s3, s21|->s5, s21|->s7, s21|->s9, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s15, s21|->s17, s21|->s19, s22|->s0, s22|->s2, s22|->s3, s22|->s6, s22|->s7, s22|->s9, s22|->s10, s22|->s12, s22|->s16, s22|->s17, s22|->s19, s22|->s21, s23|->s0, s23|->s4, s23|->s5, s23|->s6, s23|->s7, s23|->s9, s23|->s10, s23|->s11, s23|->s13, s23|->s15, s23|->s20, s24|->s4, s24|->s5, s24|->s7, s24|->s9, s24|->s10, s24|->s12, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s21, s25|->s4, s25|->s5, s25|->s6, s25|->s8, s25|->s10, s25|->s13, s25|->s14, s25|->s17, s25|->s18, s25|->s20, s25|->s21, s25|->s23, s26|->s2, s26|->s4, s26|->s5, s26|->s10, s26|->s13, s26|->s14, s26|->s15, s26|->s16, s26|->s17, s26|->s20, s26|->s25, s27|->s0, s27|->s1, s27|->s2, s27|->s4, s27|->s5, s27|->s6, s27|->s13, s27|->s19, s27|->s20, s27|->s23, s28|->s0, s28|->s1, s28|->s2, s28|->s5, s28|->s7, s28|->s10, s28|->s12, s28|->s18, s28|->s20, s28|->s21, s28|->s22, s28|->s23, s28|->s24, s28|->s25, s28|->s26, s28|->s27, s29|->s2, s29|->s3, s29|->s4, s29|->s6, s29|->s9, s29|->s15, s29|->s16, s29|->s18, s29|->s20, s29|->s22, s29|->s24, s29|->s25, s29|->s28} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r3|->r1, r3|->r2, r4|->r0, r4|->r2, r5|->r0, r5|->r2, r6|->r1, r6|->r4, r7|->r0, r7|->r2, r7|->r3, r8|->r0, r8|->r2, r8|->r4, r8|->r5, r8|->r6, r9|->r1, r9|->r2, r9|->r4, r9|->r6, r9|->r8, r10|->r1, r10|->r5, r10|->r8, r10|->r9, r11|->r2, r11|->r4, r11|->r7, r12|->r0, r12|->r1, r12|->r2, r12|->r4, r12|->r9, r13|->r0, r13|->r1, r13|->r2, r13|->r4, r14|->r0, r14|->r5, r14|->r6, r14|->r8, r14|->r10, r14|->r11, r14|->r12, r15|->r1, r15|->r4, r15|->r7, r15|->r9, r15|->r13, r15|->r14, r16|->r1, r16|->r2, r16|->r6, r16|->r10, r16|->r11, r16|->r12, r16|->r14, r16|->r15, r17|->r0, r17|->r1, r17|->r2, r17|->r3, r17|->r5, r17|->r6, r17|->r8, r17|->r11, r17|->r15, r18|->r0, r18|->r2, r18|->r3, r18|->r4, r18|->r10, r18|->r12, r18|->r13, r18|->r14, r18|->r16, r18|->r17, r19|->r0, r19|->r1, r19|->r2, r19|->r4, r19|->r5, r19|->r8, r19|->r15, r19|->r16, r19|->r18, r20|->r2, r20|->r5, r20|->r6, r20|->r9, r20|->r10, r20|->r11, r20|->r12, r20|->r14, r20|->r17, r20|->r18, r21|->r4, r21|->r6, r21|->r7, r21|->r8, r21|->r11, r21|->r12, r21|->r14, r21|->r15, r21|->r16, r21|->r19, r21|->r20, r22|->r1, r22|->r3, r22|->r5, r22|->r6, r22|->r9, r22|->r11, r22|->r12, r22|->r13, r22|->r15, r22|->r17, r23|->r0, r23|->r3, r23|->r4, r23|->r7, r23|->r9, r23|->r10, r23|->r11, r23|->r13, r23|->r14, r23|->r18, r23|->r20, r23|->r21, r24|->r1, r24|->r3, r24|->r4, r24|->r6, r24|->r7, r24|->r8, r24|->r9, r24|->r12, r24|->r14, r24|->r15, r24|->r16, r24|->r20, r24|->r21, r24|->r23, r25|->r0, r25|->r1, r25|->r2, r25|->r8, r25|->r12, r25|->r13, r25|->r14, r25|->r15, r25|->r17, r25|->r21, r25|->r22, r25|->r23, r26|->r2, r26|->r3, r26|->r5, r26|->r6, r26|->r14, r26|->r16, r26|->r18, r26|->r19, r26|->r20, r26|->r21, r26|->r22, r26|->r23, r26|->r25, r27|->r2, r27|->r5, r27|->r9, r27|->r10, r27|->r15, r27|->r17, r27|->r23, r28|->r0, r28|->r1, r28|->r7, r28|->r8, r28|->r11, r28|->r14, r28|->r16, r28|->r17, r28|->r19, r28|->r21, r28|->r23, r28|->r24, r29|->r0, r29|->r3, r29|->r6, r29|->r8, r29|->r10, r29|->r12, r29|->r14, r29|->r16, r29|->r18, r29|->r21, r29|->r25, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s12,re:r12,mo:pro,pr: 4,co:{c4,c3,c7,c2})), rule1|->(rec(su:s19,re:r28,mo:pro,pr: 4,co:{c3,c5,c9,c6,c7})), rule2|->(rec(su:s4,re:r12,mo:per,pr: 2,co:{c1,c3,c0})), rule3|->(rec(su:s7,re:r17,mo:pro,pr: 0,co:{c5,c7,c0})), rule4|->(rec(su:s11,re:r18,mo:per,pr: 0,co:{c9,c0,c1,c8})), rule5|->(rec(su:s14,re:r13,mo:pro,pr: 0,co:{c9,c8,c6,c1})), rule6|->(rec(su:s9,re:r18,mo:per,pr: 3,co:{c5,c9,c6})), rule7|->(rec(su:s26,re:r11,mo:pro,pr: 1,co:{c0,c6})), rule8|->(rec(su:s10,re:r3,mo:per,pr: 1,co:{c9,c3,c0})), rule9|->(rec(su:s27,re:r6,mo:pro,pr: 1,co:{c1})), rule10|->(rec(su:s26,re:r13,mo:pro,pr: 1,co:{c2,c1,c5,c3,c9,c8,c0})), rule11|->(rec(su:s13,re:r10,mo:pro,pr: 3,co:{c7,c1}))}

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