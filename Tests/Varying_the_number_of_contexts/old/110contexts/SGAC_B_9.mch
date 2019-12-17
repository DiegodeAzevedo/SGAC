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
    e_sub={s1|->s0, s3|->s0, s3|->s1, s4|->s1, s5|->s1, s5|->s4, s6|->s1, s6|->s2, s6|->s5, s8|->s0, s8|->s3, s8|->s4, s8|->s5, s8|->s6, s8|->s7, s9|->s5, s9|->s8, s10|->s1, s10|->s4, s10|->s5, s10|->s7, s10|->s8, s11|->s0, s11|->s1, s11|->s2, s11|->s5, s11|->s7, s12|->s2, s12|->s6, s12|->s8, s12|->s11, s13|->s0, s13|->s5, s13|->s7, s13|->s11, s13|->s12, s14|->s0, s14|->s2, s14|->s4, s14|->s7, s14|->s9, s14|->s10, s14|->s13, s15|->s2, s15|->s3, s15|->s4, s15|->s6, s15|->s11, s15|->s13, s15|->s14, s16|->s0, s16|->s4, s16|->s5, s16|->s11, s16|->s12, s16|->s13, s16|->s14, s16|->s15, s17|->s0, s17|->s1, s17|->s2, s17|->s4, s17|->s5, s17|->s7, s17|->s9, s17|->s11, s17|->s12, s17|->s13, s17|->s15, s18|->s3, s18|->s6, s18|->s9, s18|->s14, s18|->s15, s18|->s17, s19|->s0, s19|->s1, s19|->s3, s19|->s4, s19|->s5, s19|->s8, s19|->s10, s19|->s11, s19|->s12, s19|->s16, s19|->s17, s20|->s2, s20|->s6, s20|->s7, s20|->s8, s20|->s11, s20|->s15, s20|->s19, s21|->s0, s21|->s1, s21|->s3, s21|->s4, s21|->s5, s21|->s7, s21|->s8, s21|->s10, s21|->s12, s21|->s15, s21|->s17, s21|->s19, s21|->s20, s22|->s0, s22|->s4, s22|->s5, s22|->s8, s22|->s10, s22|->s15, s22|->s16, s22|->s17, s22|->s19, s22|->s20, s22|->s21, s23|->s0, s23|->s2, s23|->s4, s23|->s5, s23|->s6, s23|->s9, s23|->s12, s23|->s13, s23|->s14, s23|->s15, s23|->s19, s23|->s22, s24|->s1, s24|->s4, s24|->s6, s24|->s8, s24|->s11, s24|->s12, s24|->s13, s24|->s14, s24|->s15, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s20, s24|->s23, s25|->s0, s25|->s2, s25|->s3, s25|->s4, s25|->s5, s25|->s6, s25|->s12, s25|->s14, s25|->s16, s25|->s17, s25|->s18, s25|->s19, s25|->s20, s25|->s21, s25|->s24, s26|->s0, s26|->s1, s26|->s2, s26|->s3, s26|->s9, s26|->s10, s26|->s14, s26|->s17, s26|->s20, s26|->s21, s26|->s23, s26|->s25, s27|->s6, s27|->s7, s27|->s8, s27|->s9, s27|->s12, s27|->s13, s27|->s14, s27|->s17, s27|->s18, s27|->s19, s27|->s20, s27|->s21, s27|->s23, s27|->s26, s28|->s3, s28|->s4, s28|->s5, s28|->s6, s28|->s7, s28|->s8, s28|->s9, s28|->s11, s28|->s13, s28|->s14, s28|->s16, s28|->s18, s28|->s20, s28|->s22, s28|->s25, s29|->s3, s29|->s5, s29|->s7, s29|->s8, s29|->s10, s29|->s20, s29|->s22, s29|->s23, s29|->s27, s29|->s28} &
    e_res={r1|->r0, r2|->r0, r3|->r0, r3|->r2, r4|->r1, r4|->r2, r5|->r0, r5|->r3, r6|->r0, r6|->r4, r7|->r0, r8|->r0, r8|->r3, r8|->r7, r9|->r0, r9|->r1, r9|->r4, r9|->r6, r10|->r1, r10|->r6, r10|->r8, r10|->r9, r11|->r0, r11|->r1, r11|->r4, r11|->r5, r11|->r6, r11|->r8, r11|->r9, r12|->r0, r12|->r1, r12|->r2, r12|->r3, r12|->r4, r12|->r6, r12|->r7, r12|->r8, r12|->r9, r12|->r10, r12|->r11, r13|->r0, r13|->r2, r13|->r4, r13|->r5, r13|->r6, r13|->r7, r13|->r8, r13|->r11, r14|->r0, r14|->r4, r14|->r7, r14|->r9, r14|->r10, r15|->r0, r15|->r1, r15|->r2, r15|->r4, r15|->r7, r15|->r9, r15|->r10, r15|->r11, r15|->r12, r16|->r1, r16|->r2, r16|->r4, r16|->r13, r16|->r14, r17|->r3, r17|->r4, r17|->r7, r17|->r8, r17|->r12, r17|->r13, r17|->r14, r17|->r15, r17|->r16, r18|->r2, r18|->r4, r18|->r7, r18|->r8, r18|->r9, r18|->r10, r18|->r11, r18|->r12, r18|->r16, r19|->r0, r19|->r1, r19|->r2, r19|->r5, r19|->r6, r19|->r7, r19|->r8, r19|->r10, r19|->r16, r19|->r18, r20|->r1, r20|->r2, r20|->r6, r20|->r7, r20|->r8, r20|->r11, r20|->r13, r20|->r16, r20|->r17, r20|->r18, r20|->r19, r21|->r3, r21|->r8, r21|->r11, r21|->r15, r21|->r18, r21|->r19, r22|->r3, r22|->r4, r22|->r5, r22|->r7, r22|->r9, r22|->r14, r22|->r15, r22|->r16, r22|->r19, r22|->r20, r22|->r21, r23|->r0, r23|->r1, r23|->r2, r23|->r3, r23|->r6, r23|->r8, r23|->r10, r23|->r14, r23|->r15, r23|->r17, r23|->r18, r23|->r20, r24|->r3, r24|->r5, r24|->r6, r24|->r8, r24|->r12, r24|->r13, r24|->r14, r24|->r17, r24|->r18, r24|->r19, r24|->r20, r24|->r21, r24|->r22, r24|->r23, r25|->r3, r25|->r4, r25|->r5, r25|->r6, r25|->r8, r25|->r9, r25|->r11, r25|->r13, r25|->r17, r25|->r19, r25|->r20, r25|->r21, r26|->r0, r26|->r1, r26|->r2, r26|->r3, r26|->r8, r26|->r9, r26|->r10, r26|->r11, r26|->r13, r26|->r14, r26|->r16, r26|->r18, r26|->r20, r26|->r22, r27|->r0, r27|->r3, r27|->r4, r27|->r6, r27|->r7, r27|->r8, r27|->r10, r27|->r11, r27|->r13, r27|->r15, r27|->r16, r27|->r20, r27|->r21, r27|->r23, r27|->r26, r28|->r2, r28|->r4, r28|->r8, r28|->r9, r28|->r10, r28|->r11, r28|->r16, r28|->r22, r28|->r23, r28|->r26, r29|->r1, r29|->r4, r29|->r7, r29|->r8, r29|->r9, r29|->r11, r29|->r13, r29|->r15, r29|->r16, r29|->r17, r29|->r19, r29|->r21, r29|->r22, r29|->r25, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s13,re:r14,mo:per,pr: 1,co:{c2})), rule1|->(rec(su:s24,re:r28,mo:per,pr: 2,co:{c2,c4,c5,c9,c7})), rule2|->(rec(su:s3,re:r10,mo:pro,pr: 4,co:{c9,c6,c7,c8,c2,c0})), rule3|->(rec(su:s26,re:r26,mo:pro,pr: 1,co:{c2})), rule4|->(rec(su:s6,re:r8,mo:pro,pr: 0,co:{c1,c8,c0,c9,c4,c6,c7})), rule5|->(rec(su:s6,re:r12,mo:per,pr: 1,co:{c9,c6,c1,c0})), rule6|->(rec(su:s12,re:r8,mo:per,pr: 0,co:{c6})), rule7|->(rec(su:s25,re:r9,mo:per,pr: 0,co:{c4,c8,c0,c9,c6,c3})), rule8|->(rec(su:s24,re:r4,mo:per,pr: 0,co:{c7,c4,c1,c5,c8})), rule9|->(rec(su:s22,re:r16,mo:pro,pr: 0,co:{c8,c5,c6,c9,c7,c1})), rule10|->(rec(su:s15,re:r25,mo:per,pr: 3,co:{c5,c7})), rule11|->(rec(su:s16,re:r27,mo:pro,pr: 1,co:{c0,c2,c7,c6}))}

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