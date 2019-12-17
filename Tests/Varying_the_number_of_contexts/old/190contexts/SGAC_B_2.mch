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
    e_sub={s2|->s0, s3|->s1, s4|->s2, s4|->s3, s5|->s0, s5|->s1, s5|->s2, s5|->s4, s6|->s2, s6|->s3, s6|->s4, s7|->s0, s7|->s3, s7|->s4, s7|->s5, s7|->s6, s8|->s2, s8|->s3, s8|->s4, s8|->s6, s8|->s7, s9|->s0, s9|->s1, s9|->s2, s9|->s3, s9|->s4, s9|->s5, s9|->s6, s10|->s0, s10|->s3, s10|->s4, s10|->s5, s10|->s9, s11|->s0, s11|->s4, s11|->s5, s11|->s7, s11|->s10, s12|->s3, s12|->s4, s12|->s9, s12|->s11, s13|->s0, s13|->s4, s13|->s8, s13|->s11, s13|->s12, s14|->s3, s14|->s4, s14|->s5, s14|->s6, s14|->s7, s14|->s13, s15|->s0, s15|->s4, s15|->s7, s15|->s8, s16|->s0, s16|->s5, s16|->s6, s16|->s7, s16|->s8, s16|->s10, s16|->s12, s17|->s1, s17|->s2, s17|->s3, s17|->s5, s17|->s7, s17|->s8, s17|->s9, s17|->s13, s17|->s16, s18|->s0, s18|->s1, s18|->s2, s18|->s3, s18|->s4, s18|->s5, s18|->s8, s18|->s9, s18|->s11, s18|->s12, s18|->s14, s18|->s16, s19|->s0, s19|->s1, s19|->s4, s19|->s5, s19|->s6, s19|->s11, s19|->s13, s19|->s14, s19|->s15, s19|->s17, s19|->s18, s20|->s0, s20|->s1, s20|->s2, s20|->s5, s20|->s6, s20|->s8, s20|->s11, s20|->s12, s20|->s14, s20|->s16, s20|->s17, s20|->s18, s20|->s19, s21|->s0, s21|->s2, s21|->s3, s21|->s4, s21|->s7, s21|->s8, s21|->s12, s21|->s13, s21|->s15, s21|->s17, s21|->s18, s21|->s19, s22|->s2, s22|->s6, s22|->s7, s22|->s11, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s18, s22|->s20, s22|->s21, s23|->s0, s23|->s1, s23|->s5, s23|->s6, s23|->s7, s23|->s8, s23|->s9, s23|->s10, s23|->s11, s23|->s12, s23|->s15, s23|->s16, s23|->s17, s23|->s19, s23|->s21, s24|->s0, s24|->s2, s24|->s3, s24|->s4, s24|->s7, s24|->s10, s24|->s16, s24|->s17, s24|->s23, s25|->s3, s25|->s4, s25|->s5, s25|->s8, s25|->s10, s25|->s11, s25|->s20, s25|->s22, s25|->s23, s25|->s24, s26|->s0, s26|->s8, s26|->s11, s26|->s12, s26|->s14, s26|->s16, s26|->s17, s26|->s18, s26|->s19, s26|->s20, s26|->s22, s26|->s24, s26|->s25, s27|->s1, s27|->s2, s27|->s3, s27|->s4, s27|->s7, s27|->s10, s27|->s11, s27|->s12, s27|->s13, s27|->s14, s27|->s15, s27|->s17, s27|->s19, s27|->s21, s27|->s22, s27|->s23, s27|->s25, s27|->s26, s28|->s4, s28|->s6, s28|->s7, s28|->s8, s28|->s9, s28|->s11, s28|->s12, s28|->s13, s28|->s14, s28|->s16, s28|->s18, s28|->s19, s28|->s21, s28|->s22, s28|->s23, s28|->s24, s28|->s27, s29|->s0, s29|->s1, s29|->s3, s29|->s6, s29|->s9, s29|->s10, s29|->s11, s29|->s13, s29|->s14, s29|->s18, s29|->s19, s29|->s20, s29|->s21, s29|->s23} &
    e_res={r2|->r0, r2|->r1, r3|->r0, r3|->r2, r4|->r0, r4|->r2, r4|->r3, r5|->r2, r6|->r1, r6|->r5, r7|->r0, r7|->r1, r7|->r2, r7|->r4, r8|->r1, r8|->r2, r8|->r7, r9|->r0, r9|->r1, r9|->r2, r9|->r6, r9|->r7, r9|->r8, r10|->r1, r10|->r3, r10|->r4, r10|->r5, r10|->r6, r10|->r7, r10|->r8, r11|->r0, r11|->r5, r11|->r6, r12|->r1, r12|->r2, r12|->r4, r12|->r6, r12|->r7, r12|->r8, r12|->r9, r12|->r10, r13|->r3, r13|->r5, r13|->r9, r13|->r11, r13|->r12, r14|->r0, r14|->r2, r14|->r3, r14|->r8, r14|->r11, r14|->r12, r14|->r13, r15|->r0, r15|->r3, r15|->r7, r15|->r8, r15|->r9, r15|->r11, r15|->r12, r16|->r0, r16|->r1, r16|->r2, r16|->r3, r16|->r5, r16|->r6, r16|->r7, r16|->r8, r16|->r10, r16|->r11, r16|->r12, r16|->r13, r16|->r14, r17|->r0, r17|->r1, r17|->r2, r17|->r3, r17|->r4, r17|->r8, r17|->r10, r17|->r11, r17|->r12, r17|->r14, r17|->r15, r17|->r16, r18|->r2, r18|->r4, r18|->r5, r18|->r6, r18|->r15, r19|->r0, r19|->r2, r19|->r6, r19|->r7, r19|->r9, r19|->r10, r19|->r12, r19|->r14, r19|->r17, r19|->r18, r20|->r0, r20|->r6, r20|->r9, r20|->r11, r20|->r14, r20|->r15, r20|->r16, r20|->r17, r20|->r18, r20|->r19, r21|->r4, r21|->r5, r21|->r6, r21|->r7, r21|->r9, r21|->r12, r21|->r14, r21|->r15, r21|->r16, r21|->r17, r22|->r2, r22|->r3, r22|->r4, r22|->r5, r22|->r6, r22|->r7, r22|->r8, r22|->r10, r22|->r14, r22|->r16, r22|->r19, r22|->r21, r23|->r1, r23|->r6, r23|->r8, r23|->r9, r23|->r10, r23|->r17, r23|->r19, r23|->r21, r24|->r0, r24|->r1, r24|->r2, r24|->r7, r24|->r12, r24|->r13, r24|->r14, r24|->r15, r24|->r16, r24|->r19, r24|->r20, r24|->r21, r24|->r23, r25|->r1, r25|->r2, r25|->r6, r25|->r7, r25|->r8, r25|->r9, r25|->r10, r25|->r11, r25|->r13, r25|->r17, r25|->r19, r25|->r21, r25|->r23, r26|->r2, r26|->r5, r26|->r6, r26|->r7, r26|->r9, r26|->r11, r26|->r12, r26|->r14, r26|->r17, r26|->r19, r26|->r20, r26|->r24, r27|->r2, r27|->r4, r27|->r5, r27|->r8, r27|->r9, r27|->r12, r27|->r14, r27|->r15, r27|->r16, r27|->r18, r27|->r23, r28|->r0, r28|->r1, r28|->r2, r28|->r3, r28|->r4, r28|->r6, r28|->r10, r28|->r11, r28|->r12, r28|->r13, r28|->r18, r28|->r19, r28|->r20, r28|->r23, r28|->r27, r29|->r0, r29|->r1, r29|->r2, r29|->r4, r29|->r6, r29|->r7, r29|->r8, r29|->r9, r29|->r10, r29|->r12, r29|->r15, r29|->r17, r29|->r18, r29|->r23, r29|->r28} &
    rules={rule0|->(rec(su:s17,re:r7,mo:per,pr: 3,co:{c3})), rule1|->(rec(su:s17,re:r23,mo:pro,pr: 3,co:{c0,c6,c8,c5,c3,c7,c9})), rule2|->(rec(su:s10,re:r15,mo:pro,pr: 0,co:{c1})), rule3|->(rec(su:s12,re:r17,mo:per,pr: 2,co:{c3,c6,c2})), rule4|->(rec(su:s9,re:r2,mo:pro,pr: 0,co:{c7,c3,c5})), rule5|->(rec(su:s10,re:r12,mo:per,pr: 3,co:{c9,c8})), rule6|->(rec(su:s23,re:r12,mo:pro,pr: 4,co:{c1,c0,c3,c7,c6})), rule7|->(rec(su:s9,re:r13,mo:pro,pr: 2,co:{c1,c6,c2,c9})), rule8|->(rec(su:s11,re:r5,mo:pro,pr: 0,co:{c0,c5,c1,c4,c3})), rule9|->(rec(su:s7,re:r28,mo:per,pr: 2,co:{c5,c2,c3,c9,c1})), rule10|->(rec(su:s24,re:r9,mo:per,pr: 3,co:{c0})), rule11|->(rec(su:s8,re:r13,mo:per,pr: 1,co:{c5,c1,c9,c0,c7,c3}))}

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