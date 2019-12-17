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
    e_sub={s1|->s0, s2|->s1, s3|->s0, s3|->s1, s3|->s2, s4|->s0, s4|->s1, s4|->s2, s5|->s1, s5|->s2, s5|->s3, s6|->s2, s6|->s4, s7|->s0, s7|->s6, s8|->s0, s8|->s3, s8|->s5, s8|->s7, s9|->s0, s9|->s2, s9|->s7, s9|->s8, s10|->s0, s10|->s5, s11|->s1, s11|->s2, s11|->s3, s11|->s4, s11|->s5, s11|->s7, s11|->s8, s11|->s9, s12|->s1, s12|->s5, s12|->s6, s12|->s8, s13|->s1, s13|->s6, s13|->s8, s13|->s9, s13|->s12, s14|->s0, s14|->s3, s14|->s4, s14|->s7, s14|->s8, s14|->s12, s15|->s0, s15|->s7, s15|->s8, s15|->s9, s15|->s12, s15|->s13, s16|->s4, s16|->s5, s16|->s8, s16|->s9, s16|->s11, s16|->s12, s16|->s14, s17|->s1, s17|->s6, s17|->s8, s17|->s12, s17|->s14, s17|->s15, s18|->s2, s18|->s3, s18|->s4, s18|->s7, s18|->s8, s18|->s12, s18|->s13, s18|->s14, s18|->s15, s18|->s17, s19|->s1, s19|->s3, s19|->s5, s19|->s6, s19|->s9, s19|->s11, s19|->s12, s19|->s13, s19|->s14, s19|->s15, s19|->s18, s20|->s0, s20|->s1, s20|->s3, s20|->s4, s20|->s5, s20|->s9, s20|->s10, s20|->s11, s20|->s12, s20|->s14, s20|->s15, s20|->s16, s20|->s17, s20|->s18, s20|->s19, s21|->s0, s21|->s4, s21|->s5, s21|->s7, s21|->s10, s21|->s16, s21|->s17, s21|->s18, s21|->s20, s22|->s2, s22|->s3, s22|->s5, s22|->s7, s22|->s9, s22|->s10, s22|->s11, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s19, s22|->s20, s22|->s21, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s5, s23|->s8, s23|->s12, s23|->s13, s23|->s17, s23|->s18, s23|->s20, s23|->s21, s24|->s0, s24|->s2, s24|->s3, s24|->s6, s24|->s7, s24|->s8, s24|->s9, s24|->s11, s24|->s17, s24|->s22, s24|->s23, s25|->s4, s25|->s5, s25|->s6, s25|->s7, s25|->s10, s25|->s12, s25|->s16, s25|->s18, s25|->s19, s25|->s20, s25|->s22, s25|->s23, s26|->s0, s26|->s1, s26|->s3, s26|->s4, s26|->s5, s26|->s8, s26|->s9, s26|->s11, s26|->s12, s26|->s13, s26|->s15, s26|->s16, s26|->s20, s26|->s22, s27|->s0, s27|->s1, s27|->s4, s27|->s5, s27|->s6, s27|->s7, s27|->s8, s27|->s10, s27|->s14, s27|->s15, s27|->s16, s27|->s17, s27|->s18, s27|->s23, s27|->s24, s27|->s26, s28|->s1, s28|->s2, s28|->s6, s28|->s7, s28|->s8, s28|->s11, s28|->s12, s28|->s15, s28|->s17, s28|->s19, s28|->s20, s28|->s21, s28|->s22, s28|->s23, s28|->s24, s28|->s25, s28|->s27, s29|->s0, s29|->s3, s29|->s4, s29|->s7, s29|->s8, s29|->s10, s29|->s12, s29|->s13, s29|->s18, s29|->s19, s29|->s20, s29|->s21, s29|->s22, s29|->s25, s29|->s26, s29|->s27, s29|->s28} &
    e_res={r1|->r0, r3|->r2, r4|->r0, r4|->r1, r4|->r3, r5|->r0, r5|->r3, r5|->r4, r6|->r0, r6|->r2, r6|->r4, r6|->r5, r7|->r0, r7|->r2, r7|->r3, r7|->r4, r7|->r6, r8|->r1, r8|->r5, r8|->r6, r9|->r0, r9|->r2, r9|->r3, r9|->r4, r9|->r5, r10|->r7, r10|->r9, r11|->r0, r11|->r1, r11|->r2, r11|->r4, r11|->r5, r11|->r7, r11|->r8, r12|->r1, r12|->r3, r12|->r4, r12|->r5, r12|->r10, r13|->r1, r13|->r8, r13|->r9, r13|->r10, r13|->r12, r14|->r0, r14|->r1, r14|->r6, r14|->r8, r14|->r9, r14|->r10, r14|->r12, r14|->r13, r15|->r0, r15|->r4, r15|->r5, r15|->r6, r15|->r8, r15|->r9, r15|->r11, r15|->r13, r15|->r14, r16|->r1, r16|->r4, r16|->r6, r16|->r7, r16|->r8, r16|->r10, r16|->r11, r16|->r12, r16|->r13, r16|->r14, r16|->r15, r17|->r3, r17|->r6, r17|->r13, r18|->r0, r18|->r2, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r7, r18|->r8, r18|->r11, r18|->r12, r18|->r13, r18|->r14, r18|->r15, r18|->r16, r19|->r0, r19|->r2, r19|->r3, r19|->r4, r19|->r5, r19|->r6, r19|->r9, r19|->r15, r19|->r16, r19|->r17, r19|->r18, r20|->r1, r20|->r3, r20|->r6, r20|->r7, r20|->r8, r20|->r9, r20|->r15, r20|->r16, r20|->r19, r21|->r0, r21|->r1, r21|->r2, r21|->r4, r21|->r7, r21|->r8, r21|->r13, r21|->r14, r21|->r15, r21|->r17, r21|->r18, r21|->r19, r22|->r0, r22|->r1, r22|->r2, r22|->r3, r22|->r4, r22|->r5, r22|->r6, r22|->r7, r22|->r8, r22|->r12, r22|->r13, r22|->r14, r22|->r15, r22|->r20, r23|->r2, r23|->r3, r23|->r5, r23|->r7, r23|->r8, r23|->r12, r23|->r13, r23|->r18, r23|->r19, r23|->r20, r23|->r21, r23|->r22, r24|->r0, r24|->r2, r24|->r3, r24|->r5, r24|->r6, r24|->r7, r24|->r10, r24|->r14, r24|->r16, r24|->r20, r24|->r22, r25|->r2, r25|->r3, r25|->r6, r25|->r8, r25|->r9, r25|->r11, r25|->r12, r25|->r13, r25|->r14, r25|->r16, r25|->r21, r25|->r22, r25|->r23, r25|->r24, r26|->r1, r26|->r2, r26|->r3, r26|->r5, r26|->r9, r26|->r11, r26|->r13, r26|->r21, r26|->r22, r26|->r23, r27|->r0, r27|->r1, r27|->r2, r27|->r4, r27|->r8, r27|->r12, r27|->r14, r27|->r15, r27|->r18, r27|->r19, r27|->r22, r27|->r23, r27|->r25, r28|->r0, r28|->r1, r28|->r5, r28|->r6, r28|->r8, r28|->r10, r28|->r13, r28|->r14, r28|->r15, r28|->r16, r28|->r17, r28|->r19, r28|->r25, r29|->r3, r29|->r4, r29|->r5, r29|->r10, r29|->r11, r29|->r12, r29|->r19, r29|->r23, r29|->r24, r29|->r25, r29|->r26, r29|->r28} &
    rules={rule0|->(rec(su:s7,re:r27,mo:pro,pr: 4,co:{c7,c1,c5,c6,c2})), rule1|->(rec(su:s3,re:r2,mo:per,pr: 3,co:{c2,c7,c5,c6,c0})), rule2|->(rec(su:s24,re:r11,mo:pro,pr: 2,co:{c5,c8})), rule3|->(rec(su:s8,re:r16,mo:per,pr: 3,co:{c2,c6})), rule4|->(rec(su:s14,re:r9,mo:pro,pr: 1,co:{c2,c5,c4,c1,c7,c9})), rule5|->(rec(su:s14,re:r6,mo:pro,pr: 3,co:{c0,c1,c6,c4,c3})), rule6|->(rec(su:s26,re:r2,mo:pro,pr: 0,co:{c3,c4,c9,c2,c8})), rule7|->(rec(su:s11,re:r12,mo:pro,pr: 4,co:{c6,c7,c2,c5})), rule8|->(rec(su:s20,re:r9,mo:per,pr: 1,co:{c2,c7,c9,c8,c3,c0,c1})), rule9|->(rec(su:s0,re:r14,mo:per,pr: 2,co:{c5,c8})), rule10|->(rec(su:s25,re:r8,mo:pro,pr: 1,co:{c9,c7,c6})), rule11|->(rec(su:s25,re:r2,mo:per,pr: 2,co:{c9,c5,c4,c8,c2,c1}))}

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