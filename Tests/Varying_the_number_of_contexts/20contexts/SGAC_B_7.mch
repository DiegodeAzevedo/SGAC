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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s3|->s0, s3|->s1, s4|->s3, s6|->s0, s6|->s2, s6|->s3, s7|->s0, s7|->s1, s7|->s2, s7|->s3, s8|->s0, s8|->s2, s8|->s3, s8|->s4, s8|->s6, s8|->s7, s9|->s6, s10|->s0, s10|->s1, s10|->s2, s10|->s6, s10|->s7, s11|->s0, s11|->s3, s11|->s5, s11|->s8, s11|->s9, s11|->s10, s12|->s0, s12|->s3, s12|->s4, s12|->s9, s12|->s10, s12|->s11, s13|->s0, s13|->s1, s13|->s4, s13|->s5, s13|->s8, s13|->s10, s13|->s11, s14|->s2, s14|->s5, s14|->s6, s14|->s7, s14|->s10, s14|->s11, s14|->s12, s14|->s13, s15|->s1, s15|->s3, s15|->s4, s15|->s6, s15|->s7, s15|->s10, s15|->s12, s15|->s14, s16|->s1, s16|->s2, s16|->s3, s16|->s5, s16|->s6, s16|->s7, s16|->s8, s16|->s11, s16|->s12, s16|->s13, s17|->s0, s17|->s1, s17|->s6, s17|->s7, s17|->s8, s17|->s9, s17|->s10, s17|->s12, s17|->s14, s17|->s15, s18|->s0, s18|->s2, s18|->s3, s18|->s5, s18|->s6, s18|->s7, s18|->s8, s18|->s9, s18|->s11, s18|->s15, s19|->s0, s19|->s1, s19|->s9, s19|->s11, s19|->s13, s19|->s16, s19|->s17, s19|->s18, s20|->s0, s20|->s6, s20|->s8, s20|->s10, s20|->s13, s20|->s14, s20|->s15, s20|->s16, s21|->s0, s21|->s1, s21|->s2, s21|->s3, s21|->s6, s21|->s7, s21|->s8, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s16, s21|->s17, s21|->s18, s21|->s19, s22|->s4, s22|->s5, s22|->s7, s22|->s10, s22|->s12, s22|->s14, s22|->s15, s22|->s16, s22|->s21, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s4, s23|->s5, s23|->s6, s23|->s8, s23|->s10, s23|->s13, s23|->s15, s23|->s16, s23|->s17, s23|->s20, s24|->s1, s24|->s11, s24|->s16, s24|->s20, s24|->s21, s24|->s23, s25|->s0, s25|->s1, s25|->s2, s25|->s3, s25|->s5, s25|->s6, s25|->s7, s25|->s9, s25|->s12, s25|->s13, s25|->s15, s25|->s18, s25|->s23, s25|->s24, s26|->s0, s26|->s2, s26|->s3, s26|->s4, s26|->s6, s26|->s10, s26|->s12, s26|->s13, s26|->s16, s26|->s17, s26|->s18, s26|->s19, s26|->s21, s26|->s22, s26|->s23, s26|->s24, s27|->s0, s27|->s1, s27|->s3, s27|->s5, s27|->s6, s27|->s9, s27|->s11, s27|->s14, s27|->s15, s27|->s23, s27|->s25, s28|->s0, s28|->s1, s28|->s2, s28|->s3, s28|->s4, s28|->s8, s28|->s13, s28|->s14, s28|->s15, s28|->s16, s28|->s17, s28|->s19, s28|->s21, s28|->s22, s28|->s23, s28|->s24, s28|->s25, s28|->s26, s29|->s3, s29|->s6, s29|->s7, s29|->s9, s29|->s11, s29|->s16, s29|->s17, s29|->s18, s29|->s22, s29|->s23, s29|->s25, s29|->s26} &
    e_res={r3|->r2, r4|->r2, r5|->r1, r5|->r2, r6|->r0, r6|->r3, r6|->r4, r6|->r5, r7|->r2, r7|->r3, r7|->r4, r7|->r5, r7|->r6, r8|->r0, r8|->r1, r8|->r3, r8|->r5, r9|->r4, r9|->r7, r9|->r8, r10|->r2, r10|->r3, r10|->r5, r10|->r6, r10|->r7, r10|->r8, r11|->r0, r11|->r1, r11|->r2, r11|->r3, r11|->r4, r11|->r6, r11|->r7, r11|->r8, r11|->r9, r11|->r10, r12|->r1, r12|->r2, r12|->r4, r12|->r5, r12|->r6, r12|->r8, r12|->r10, r12|->r11, r13|->r0, r13|->r2, r13|->r3, r13|->r5, r13|->r10, r13|->r12, r14|->r0, r14|->r6, r14|->r9, r14|->r10, r14|->r12, r15|->r0, r15|->r1, r15|->r3, r15|->r10, r15|->r11, r15|->r12, r15|->r13, r16|->r0, r16|->r2, r16|->r3, r16|->r4, r16|->r7, r16|->r8, r16|->r9, r16|->r10, r16|->r12, r16|->r14, r17|->r2, r17|->r6, r17|->r7, r17|->r9, r17|->r10, r17|->r11, r17|->r13, r17|->r14, r17|->r16, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r9, r18|->r10, r18|->r13, r18|->r16, r18|->r17, r19|->r0, r19|->r2, r19|->r3, r19|->r7, r19|->r10, r19|->r11, r19|->r14, r19|->r16, r20|->r0, r20|->r3, r20|->r8, r20|->r11, r20|->r12, r20|->r14, r20|->r18, r21|->r0, r21|->r2, r21|->r3, r21|->r7, r21|->r8, r21|->r11, r21|->r13, r21|->r15, r21|->r16, r22|->r0, r22|->r2, r22|->r3, r22|->r5, r22|->r8, r22|->r10, r22|->r12, r22|->r15, r22|->r16, r22|->r17, r22|->r18, r22|->r20, r23|->r1, r23|->r5, r23|->r7, r23|->r8, r23|->r9, r23|->r10, r23|->r13, r23|->r16, r23|->r18, r23|->r19, r23|->r22, r24|->r0, r24|->r1, r24|->r2, r24|->r3, r24|->r7, r24|->r9, r24|->r15, r24|->r16, r24|->r19, r24|->r21, r24|->r22, r24|->r23, r25|->r0, r25|->r2, r25|->r3, r25|->r6, r25|->r8, r25|->r10, r25|->r18, r25|->r19, r25|->r23, r25|->r24, r26|->r3, r26|->r4, r26|->r5, r26|->r6, r26|->r9, r26|->r10, r26|->r11, r26|->r12, r26|->r15, r26|->r17, r26|->r21, r26|->r24, r26|->r25, r27|->r0, r27|->r2, r27|->r4, r27|->r6, r27|->r7, r27|->r8, r27|->r9, r27|->r14, r27|->r15, r27|->r17, r27|->r19, r27|->r20, r27|->r21, r27|->r25, r28|->r2, r28|->r3, r28|->r4, r28|->r5, r28|->r8, r28|->r9, r28|->r11, r28|->r12, r28|->r13, r28|->r14, r28|->r16, r28|->r22, r28|->r24, r28|->r26, r28|->r27, r29|->r0, r29|->r1, r29|->r2, r29|->r3, r29|->r4, r29|->r10, r29|->r13, r29|->r14, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s24,re:r9,mo:per,pr: 4,co:{c7,c15,c5,c13,c18,c17})), rule1|->(rec(su:s12,re:r0,mo:per,pr: 2,co:{c11,c18})), rule2|->(rec(su:s3,re:r6,mo:per,pr: 4,co:{c10,c19,c2,c1,c15,c18,c3,c4,c8,c7,c14,c17})), rule3|->(rec(su:s16,re:r27,mo:pro,pr: 0,co:{c15,c7,c2,c5})), rule4|->(rec(su:s12,re:r13,mo:pro,pr: 0,co:{c11,c8,c12,c16,c4,c0,c14,c10,c13,c6})), rule5|->(rec(su:s27,re:r2,mo:per,pr: 1,co:{c7,c9,c8,c6,c10,c17,c2,c16,c15,c5,c0,c4})), rule6|->(rec(su:s19,re:r1,mo:pro,pr: 3,co:{c2,c17,c1,c15,c12,c14,c18})), rule7|->(rec(su:s4,re:r5,mo:per,pr: 4,co:{c16,c7,c15,c2,c1,c19,c6,c3,c9})), rule8|->(rec(su:s29,re:r1,mo:pro,pr: 0,co:{c1,c17,c7,c14,c8,c10,c2,c3,c0,c15})), rule9|->(rec(su:s0,re:r14,mo:pro,pr: 4,co:{c19,c6,c7,c1,c9,c4,c18,c16,c5,c12,c13,c11,c10})), rule10|->(rec(su:s15,re:r10,mo:pro,pr: 3,co:{c11,c13,c9,c10})), rule11|->(rec(su:s12,re:r12,mo:pro,pr: 0,co:{c15,c16,c0,c18,c19,c3}))}

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