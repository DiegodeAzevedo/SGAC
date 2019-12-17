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
    e_sub={s1|->s0, s2|->s0, s3|->s0, s3|->s1, s3|->s2, s4|->s1, s4|->s2, s5|->s0, s6|->s1, s6|->s3, s6|->s5, s7|->s0, s7|->s1, s7|->s2, s7|->s4, s7|->s6, s8|->s0, s8|->s2, s8|->s3, s8|->s4, s9|->s0, s9|->s2, s9|->s3, s9|->s4, s9|->s7, s9|->s8, s10|->s1, s10|->s2, s10|->s3, s10|->s4, s10|->s5, s10|->s6, s10|->s8, s10|->s9, s11|->s0, s11|->s4, s11|->s5, s11|->s6, s11|->s7, s11|->s9, s12|->s4, s12|->s6, s12|->s9, s13|->s2, s13|->s3, s13|->s4, s13|->s6, s13|->s7, s13|->s8, s13|->s12, s14|->s1, s14|->s5, s14|->s6, s14|->s8, s14|->s9, s14|->s10, s14|->s11, s15|->s0, s15|->s2, s15|->s3, s15|->s5, s15|->s10, s15|->s11, s15|->s14, s16|->s7, s16|->s8, s16|->s11, s16|->s13, s16|->s14, s16|->s15, s17|->s0, s17|->s4, s17|->s6, s17|->s7, s17|->s10, s17|->s14, s18|->s2, s18|->s7, s18|->s10, s18|->s14, s18|->s17, s19|->s0, s19|->s2, s19|->s3, s19|->s8, s19|->s10, s19|->s12, s20|->s1, s20|->s3, s20|->s4, s20|->s5, s20|->s6, s20|->s7, s20|->s8, s20|->s9, s20|->s11, s20|->s12, s20|->s13, s20|->s14, s20|->s15, s20|->s16, s21|->s6, s21|->s7, s21|->s8, s21|->s12, s21|->s13, s21|->s15, s21|->s16, s21|->s18, s21|->s19, s22|->s1, s22|->s6, s22|->s7, s22|->s8, s22|->s9, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s17, s22|->s19, s22|->s21, s23|->s1, s23|->s3, s23|->s4, s23|->s5, s23|->s6, s23|->s7, s23|->s8, s23|->s10, s23|->s11, s23|->s12, s23|->s14, s23|->s16, s23|->s17, s23|->s20, s23|->s21, s23|->s22, s24|->s1, s24|->s6, s24|->s8, s24|->s12, s24|->s16, s24|->s18, s24|->s22, s25|->s0, s25|->s2, s25|->s3, s25|->s4, s25|->s5, s25|->s7, s25|->s8, s25|->s9, s25|->s10, s25|->s13, s25|->s15, s25|->s17, s25|->s20, s25|->s21, s26|->s0, s26|->s2, s26|->s6, s26|->s7, s26|->s9, s26|->s11, s26|->s14, s26|->s15, s26|->s17, s26|->s18, s26|->s19, s26|->s21, s26|->s22, s27|->s1, s27|->s2, s27|->s4, s27|->s5, s27|->s6, s27|->s9, s27|->s10, s27|->s11, s27|->s13, s27|->s15, s27|->s17, s27|->s20, s27|->s21, s27|->s24, s27|->s26, s28|->s0, s28|->s1, s28|->s3, s28|->s4, s28|->s6, s28|->s7, s28|->s8, s28|->s15, s28|->s17, s28|->s18, s28|->s19, s28|->s22, s28|->s23, s28|->s24, s28|->s27, s29|->s1, s29|->s4, s29|->s7, s29|->s8, s29|->s12, s29|->s15, s29|->s16, s29|->s17, s29|->s18, s29|->s20, s29|->s21, s29|->s22, s29|->s23, s29|->s24, s29|->s27} &
    e_res={r3|->r1, r4|->r0, r4|->r3, r5|->r2, r5|->r4, r6|->r0, r6|->r2, r6|->r4, r7|->r2, r7|->r5, r7|->r6, r8|->r0, r8|->r3, r8|->r4, r8|->r6, r9|->r0, r9|->r1, r9|->r2, r9|->r3, r9|->r4, r9|->r6, r10|->r0, r10|->r1, r10|->r2, r10|->r6, r10|->r7, r11|->r1, r11|->r4, r11|->r5, r11|->r9, r12|->r7, r12|->r9, r13|->r0, r13|->r5, r13|->r6, r13|->r8, r13|->r9, r13|->r10, r13|->r11, r13|->r12, r14|->r0, r14|->r2, r14|->r5, r14|->r6, r14|->r8, r14|->r10, r14|->r12, r14|->r13, r15|->r0, r15|->r2, r15|->r5, r15|->r6, r15|->r10, r15|->r12, r15|->r13, r16|->r0, r16|->r2, r16|->r3, r16|->r5, r16|->r8, r16|->r11, r16|->r12, r16|->r13, r16|->r15, r17|->r2, r17|->r5, r17|->r6, r17|->r8, r17|->r10, r17|->r16, r18|->r1, r18|->r4, r18|->r5, r18|->r7, r18|->r9, r18|->r10, r18|->r11, r18|->r13, r18|->r15, r19|->r0, r19|->r2, r19|->r6, r19|->r7, r19|->r11, r19|->r12, r19|->r14, r19|->r17, r20|->r0, r20|->r1, r20|->r3, r20|->r4, r20|->r6, r20|->r7, r20|->r10, r20|->r12, r20|->r14, r20|->r17, r20|->r19, r21|->r1, r21|->r3, r21|->r4, r21|->r6, r21|->r12, r21|->r13, r21|->r14, r21|->r19, r21|->r20, r22|->r3, r22|->r4, r22|->r7, r22|->r9, r22|->r10, r22|->r12, r22|->r13, r22|->r15, r22|->r17, r22|->r19, r22|->r21, r23|->r0, r23|->r1, r23|->r5, r23|->r6, r23|->r7, r23|->r9, r23|->r10, r23|->r11, r23|->r14, r23|->r16, r23|->r17, r23|->r20, r24|->r1, r24|->r3, r24|->r4, r24|->r5, r24|->r6, r24|->r9, r24|->r10, r24|->r11, r24|->r12, r24|->r13, r24|->r14, r24|->r16, r24|->r17, r24|->r18, r24|->r19, r24|->r20, r24|->r21, r24|->r23, r25|->r3, r25|->r4, r25|->r6, r25|->r8, r25|->r9, r25|->r10, r25|->r11, r25|->r12, r25|->r14, r25|->r17, r25|->r18, r25|->r21, r25|->r23, r26|->r0, r26|->r1, r26|->r2, r26|->r3, r26|->r4, r26|->r6, r26|->r7, r26|->r13, r26|->r14, r26|->r15, r26|->r16, r26|->r19, r26|->r20, r26|->r21, r26|->r24, r26|->r25, r27|->r0, r27|->r1, r27|->r4, r27|->r6, r27|->r7, r27|->r10, r27|->r11, r27|->r15, r27|->r19, r27|->r21, r27|->r23, r27|->r24, r27|->r26, r28|->r7, r28|->r10, r28|->r13, r28|->r16, r28|->r18, r28|->r23, r29|->r0, r29|->r1, r29|->r2, r29|->r9, r29|->r10, r29|->r11, r29|->r12, r29|->r14, r29|->r16, r29|->r17, r29|->r19, r29|->r22, r29|->r24, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s5,re:r15,mo:pro,pr: 0,co:{c1,c9,c6,c0,c4,c5})), rule1|->(rec(su:s27,re:r2,mo:pro,pr: 1,co:{c8,c2,c5,c1,c0,c4})), rule2|->(rec(su:s14,re:r0,mo:pro,pr: 0,co:{c2,c0,c7,c1,c4,c8})), rule3|->(rec(su:s22,re:r27,mo:pro,pr: 1,co:{c9,c0,c6,c3})), rule4|->(rec(su:s20,re:r17,mo:per,pr: 3,co:{c3,c7,c2,c9})), rule5|->(rec(su:s21,re:r26,mo:per,pr: 2,co:{c5,c9,c0})), rule6|->(rec(su:s13,re:r0,mo:per,pr: 3,co:{c2,c3,c1,c0})), rule7|->(rec(su:s23,re:r16,mo:pro,pr: 0,co:{c4,c5})), rule8|->(rec(su:s6,re:r4,mo:per,pr: 2,co:{c3,c7,c5,c0,c2,c9,c1})), rule9|->(rec(su:s3,re:r8,mo:per,pr: 4,co:{c3,c1})), rule10|->(rec(su:s27,re:r3,mo:per,pr: 3,co:{c6})), rule11|->(rec(su:s6,re:r23,mo:pro,pr: 0,co:{c7,c4}))}

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