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
    CONTEXT={c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19};
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
    e_sub={s3|->s0, s3|->s1, s4|->s2, s5|->s3, s5|->s4, s6|->s4, s7|->s1, s7|->s6, s8|->s2, s8|->s6, s8|->s7, s9|->s0, s9|->s5, s9|->s6, s9|->s7, s10|->s3, s11|->s0, s11|->s5, s11|->s7, s12|->s0, s12|->s1, s12|->s2, s12|->s4, s12|->s8, s12|->s9, s12|->s10, s13|->s0, s13|->s6, s13|->s7, s13|->s9, s13|->s10, s14|->s0, s14|->s7, s14|->s8, s14|->s10, s14|->s11, s14|->s12, s14|->s13, s15|->s2, s15|->s3, s15|->s5, s15|->s8, s15|->s9, s15|->s10, s15|->s11, s15|->s13, s16|->s1, s16|->s2, s16|->s6, s16|->s7, s16|->s9, s16|->s11, s16|->s12, s17|->s3, s17|->s5, s17|->s9, s17|->s10, s17|->s14, s17|->s15, s18|->s0, s18|->s2, s18|->s5, s18|->s6, s18|->s7, s18|->s8, s18|->s9, s18|->s17, s19|->s0, s19|->s4, s19|->s5, s19|->s6, s19|->s7, s19|->s8, s19|->s9, s19|->s14, s19|->s15, s19|->s16, s19|->s17, s19|->s18, s20|->s0, s20|->s1, s20|->s2, s20|->s4, s20|->s7, s20|->s12, s20|->s14, s20|->s16, s20|->s19, s21|->s1, s21|->s5, s21|->s7, s21|->s12, s21|->s14, s21|->s18, s22|->s2, s22|->s5, s22|->s6, s22|->s9, s22|->s10, s22|->s11, s22|->s12, s22|->s13, s22|->s15, s22|->s17, s22|->s18, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s4, s23|->s5, s23|->s6, s23|->s10, s23|->s11, s23|->s15, s23|->s16, s23|->s17, s23|->s18, s23|->s21, s23|->s22, s24|->s1, s24|->s2, s24|->s7, s24|->s14, s24|->s17, s24|->s19, s24|->s22, s24|->s23, s25|->s0, s25|->s2, s25|->s3, s25|->s5, s25|->s6, s25|->s9, s25|->s10, s25|->s11, s25|->s12, s25|->s16, s25|->s18, s25|->s19, s25|->s20, s25|->s21, s25|->s23, s26|->s1, s26|->s2, s26|->s3, s26|->s4, s26|->s7, s26|->s9, s26|->s10, s26|->s11, s26|->s12, s26|->s13, s26|->s18, s26|->s23, s26|->s24, s26|->s25, s27|->s0, s27|->s1, s27|->s3, s27|->s4, s27|->s5, s27|->s6, s27|->s7, s27|->s9, s27|->s12, s27|->s13, s27|->s14, s27|->s15, s27|->s17, s27|->s18, s27|->s21, s27|->s22, s28|->s1, s28|->s2, s28|->s8, s28|->s10, s28|->s11, s28|->s12, s28|->s14, s28|->s17, s28|->s18, s28|->s19, s28|->s22, s28|->s24, s28|->s25, s28|->s26, s29|->s0, s29|->s2, s29|->s7, s29|->s8, s29|->s9, s29|->s11, s29|->s12, s29|->s13, s29|->s16, s29|->s17, s29|->s18, s29|->s19, s29|->s27} &
    e_res={r1|->r0, r2|->r0, r3|->r1, r3|->r2, r4|->r0, r4|->r1, r4|->r2, r5|->r1, r5|->r2, r5|->r4, r6|->r0, r6|->r2, r6|->r3, r6|->r4, r6|->r5, r7|->r2, r7|->r4, r7|->r6, r8|->r0, r8|->r1, r8|->r2, r8|->r5, r9|->r1, r9|->r4, r9|->r6, r9|->r8, r10|->r0, r10|->r1, r10|->r2, r10|->r4, r10|->r6, r10|->r7, r11|->r0, r11|->r4, r11|->r6, r11|->r8, r11|->r10, r12|->r1, r12|->r3, r12|->r5, r12|->r7, r12|->r8, r12|->r9, r12|->r10, r13|->r0, r13|->r3, r13|->r4, r13|->r7, r13|->r9, r13|->r10, r13|->r12, r14|->r0, r14|->r1, r14|->r4, r14|->r6, r14|->r9, r14|->r10, r14|->r11, r15|->r2, r15|->r5, r15|->r7, r15|->r8, r15|->r9, r15|->r11, r15|->r14, r16|->r1, r16|->r11, r16|->r12, r16|->r15, r17|->r0, r17|->r1, r17|->r2, r17|->r4, r17|->r5, r17|->r6, r17|->r8, r17|->r9, r17|->r10, r17|->r11, r17|->r12, r17|->r13, r18|->r5, r18|->r6, r18|->r7, r18|->r8, r18|->r9, r18|->r10, r18|->r13, r19|->r0, r19|->r1, r19|->r2, r19|->r3, r19|->r6, r19|->r7, r19|->r10, r19|->r13, r19|->r15, r19|->r16, r19|->r18, r20|->r0, r20|->r4, r20|->r6, r20|->r7, r20|->r8, r20|->r11, r20|->r12, r20|->r13, r20|->r14, r20|->r15, r20|->r16, r20|->r18, r21|->r2, r21|->r4, r21|->r9, r21|->r10, r21|->r11, r21|->r13, r21|->r15, r21|->r18, r21|->r19, r21|->r20, r22|->r0, r22|->r1, r22|->r2, r22|->r5, r22|->r7, r22|->r8, r22|->r11, r22|->r12, r22|->r15, r22|->r17, r22|->r18, r22|->r19, r22|->r20, r23|->r0, r23|->r2, r23|->r3, r23|->r5, r23|->r6, r23|->r11, r23|->r18, r23|->r19, r23|->r20, r24|->r2, r24|->r4, r24|->r8, r24|->r9, r24|->r11, r24|->r12, r24|->r14, r24|->r15, r24|->r16, r24|->r17, r24|->r18, r24|->r19, r24|->r20, r24|->r22, r24|->r23, r25|->r2, r25|->r3, r25|->r4, r25|->r5, r25|->r10, r25|->r14, r25|->r18, r25|->r19, r25|->r20, r25|->r21, r26|->r3, r26|->r4, r26|->r6, r26|->r7, r26|->r9, r26|->r11, r26|->r12, r26|->r13, r26|->r15, r26|->r18, r26|->r19, r26|->r22, r26|->r23, r26|->r24, r27|->r2, r27|->r4, r27|->r6, r27|->r7, r27|->r8, r27|->r11, r27|->r13, r27|->r18, r27|->r19, r27|->r20, r27|->r23, r28|->r1, r28|->r6, r28|->r8, r28|->r9, r28|->r10, r28|->r12, r28|->r15, r28|->r16, r28|->r17, r28|->r19, r28|->r20, r28|->r22, r28|->r23, r28|->r25, r28|->r27, r29|->r0, r29|->r2, r29|->r8, r29|->r9, r29|->r12, r29|->r13, r29|->r14, r29|->r18, r29|->r19, r29|->r21, r29|->r25, r29|->r26} &
    rules={rule0|->(rec(su:s17,re:r25,mo:per,pr: 1,co:{c11,c4})), rule1|->(rec(su:s3,re:r9,mo:per,pr: 0,co:{c4,c3,c11,c2,c9,c8,c19,c7,c1,c18})), rule2|->(rec(su:s18,re:r8,mo:pro,pr: 2,co:{c14,c4,c6,c11,c8,c12,c5,c10,c0,c2,c18,c1,c15,c13,c7})), rule3|->(rec(su:s9,re:r4,mo:per,pr: 0,co:{c14,c16,c2,c12,c0,c11})), rule4|->(rec(su:s4,re:r23,mo:pro,pr: 1,co:{c17,c13,c3,c6,c5,c14,c7,c9,c4,c2,c16})), rule5|->(rec(su:s22,re:r11,mo:pro,pr: 2,co:{c11,c1,c7,c6})), rule6|->(rec(su:s19,re:r25,mo:per,pr: 2,co:{c1,c9,c12,c18,c13,c15,c17,c3,c7,c5,c8,c11})), rule7|->(rec(su:s16,re:r9,mo:pro,pr: 4,co:{c7,c18,c6,c17,c19,c12})), rule8|->(rec(su:s9,re:r0,mo:pro,pr: 4,co:{c11,c13,c5,c17,c16,c3,c14,c0})), rule9|->(rec(su:s2,re:r14,mo:per,pr: 1,co:{c1,c13,c3})), rule10|->(rec(su:s9,re:r28,mo:pro,pr: 2,co:{c3,c4,c19,c9,c0,c16,c2,c12,c7,c14,c6,c5,c8})), rule11|->(rec(su:s0,re:r4,mo:per,pr: 1,co:{c16,c7,c3,c14,c15,c19,c13}))}

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