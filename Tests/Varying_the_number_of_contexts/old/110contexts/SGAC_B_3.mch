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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s3|->s0, s3|->s1, s4|->s1, s4|->s3, s5|->s0, s5|->s2, s5|->s4, s6|->s1, s6|->s4, s7|->s1, s7|->s3, s7|->s4, s8|->s1, s8|->s2, s8|->s5, s8|->s7, s9|->s0, s9|->s1, s9|->s3, s9|->s5, s9|->s8, s10|->s0, s10|->s4, s10|->s7, s10|->s8, s10|->s9, s11|->s1, s11|->s2, s11|->s3, s11|->s4, s11|->s8, s11|->s9, s11|->s10, s12|->s0, s12|->s8, s12|->s9, s12|->s10, s12|->s11, s13|->s0, s13|->s3, s13|->s4, s13|->s5, s13|->s6, s13|->s7, s13|->s9, s13|->s11, s13|->s12, s14|->s0, s14|->s3, s14|->s4, s14|->s7, s14|->s9, s15|->s1, s15|->s3, s15|->s4, s15|->s5, s15|->s7, s15|->s11, s15|->s14, s16|->s1, s16|->s2, s16|->s3, s16|->s5, s16|->s11, s17|->s0, s17|->s1, s17|->s2, s17|->s3, s17|->s6, s17|->s7, s17|->s8, s17|->s9, s17|->s10, s17|->s14, s17|->s16, s18|->s0, s18|->s1, s18|->s3, s18|->s5, s18|->s6, s18|->s7, s18|->s10, s18|->s11, s18|->s13, s19|->s0, s19|->s4, s19|->s5, s19|->s6, s19|->s8, s19|->s9, s19|->s12, s19|->s13, s19|->s14, s19|->s15, s19|->s16, s19|->s18, s20|->s1, s20|->s2, s20|->s5, s20|->s9, s20|->s12, s20|->s15, s20|->s19, s21|->s2, s21|->s3, s21|->s6, s21|->s7, s21|->s9, s21|->s10, s21|->s11, s21|->s12, s21|->s13, s21|->s16, s21|->s17, s21|->s18, s22|->s0, s22|->s1, s22|->s2, s22|->s3, s22|->s4, s22|->s5, s22|->s6, s22|->s9, s22|->s14, s22|->s15, s22|->s16, s22|->s19, s22|->s20, s22|->s21, s23|->s0, s23|->s5, s23|->s7, s23|->s8, s23|->s14, s23|->s15, s23|->s16, s23|->s18, s23|->s19, s23|->s20, s24|->s3, s24|->s4, s24|->s6, s24|->s12, s24|->s13, s24|->s14, s24|->s17, s24|->s19, s24|->s20, s24|->s21, s24|->s23, s25|->s1, s25|->s2, s25|->s3, s25|->s4, s25|->s11, s25|->s13, s25|->s14, s25|->s17, s25|->s21, s25|->s24, s26|->s3, s26|->s4, s26|->s10, s26|->s12, s26|->s13, s26|->s15, s26|->s16, s26|->s17, s26|->s21, s26|->s22, s26|->s23, s26|->s25, s27|->s0, s27|->s1, s27|->s3, s27|->s6, s27|->s7, s27|->s8, s27|->s11, s27|->s18, s27|->s20, s27|->s23, s27|->s24, s27|->s26, s28|->s1, s28|->s2, s28|->s4, s28|->s5, s28|->s6, s28|->s7, s28|->s9, s28|->s11, s28|->s12, s28|->s14, s28|->s15, s28|->s21, s28|->s23, s28|->s26, s29|->s1, s29|->s2, s29|->s3, s29|->s4, s29|->s5, s29|->s6, s29|->s8, s29|->s9, s29|->s10, s29|->s11, s29|->s13, s29|->s14, s29|->s15, s29|->s18, s29|->s19, s29|->s20, s29|->s22, s29|->s23, s29|->s25, s29|->s28} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r4|->r0, r4|->r1, r4|->r2, r5|->r0, r5|->r2, r5|->r4, r6|->r0, r6|->r1, r6|->r2, r6|->r5, r7|->r2, r7|->r6, r8|->r0, r8|->r2, r8|->r5, r8|->r7, r9|->r0, r9|->r2, r9|->r3, r9|->r4, r9|->r6, r9|->r8, r10|->r3, r10|->r5, r10|->r7, r10|->r8, r11|->r0, r11|->r2, r11|->r4, r11|->r5, r11|->r6, r11|->r7, r11|->r9, r11|->r10, r12|->r0, r12|->r3, r12|->r7, r12|->r9, r12|->r10, r12|->r11, r13|->r0, r13|->r3, r13|->r4, r13|->r9, r13|->r10, r14|->r6, r14|->r7, r14|->r9, r14|->r10, r14|->r11, r15|->r0, r15|->r6, r15|->r10, r16|->r4, r16|->r11, r16|->r12, r17|->r0, r17|->r1, r17|->r3, r17|->r7, r17|->r8, r17|->r9, r17|->r10, r17|->r13, r17|->r14, r17|->r15, r18|->r3, r18|->r4, r18|->r5, r18|->r7, r18|->r9, r18|->r10, r18|->r12, r18|->r14, r19|->r2, r19|->r5, r19|->r7, r19|->r8, r19|->r9, r19|->r10, r19|->r11, r19|->r12, r19|->r15, r19|->r17, r19|->r18, r20|->r2, r20|->r3, r20|->r7, r20|->r8, r20|->r10, r20|->r11, r20|->r12, r20|->r14, r20|->r15, r20|->r17, r20|->r18, r21|->r0, r21|->r1, r21|->r2, r21|->r5, r21|->r6, r21|->r7, r21|->r11, r21|->r15, r21|->r17, r21|->r19, r21|->r20, r22|->r0, r22|->r2, r22|->r5, r22|->r6, r22|->r9, r22|->r12, r22|->r13, r22|->r16, r22|->r18, r23|->r0, r23|->r2, r23|->r3, r23|->r6, r23|->r10, r23|->r11, r23|->r16, r23|->r21, r23|->r22, r24|->r4, r24|->r5, r24|->r6, r24|->r7, r24|->r8, r24|->r10, r24|->r11, r24|->r12, r24|->r13, r24|->r14, r24|->r16, r24|->r17, r24|->r18, r24|->r19, r24|->r20, r24|->r21, r25|->r0, r25|->r4, r25|->r5, r25|->r6, r25|->r7, r25|->r9, r25|->r10, r25|->r12, r25|->r16, r25|->r17, r25|->r18, r25|->r20, r25|->r21, r25|->r22, r25|->r24, r26|->r0, r26|->r2, r26|->r3, r26|->r5, r26|->r6, r26|->r8, r26|->r9, r26|->r10, r26|->r14, r26|->r15, r26|->r16, r26|->r17, r26|->r18, r26|->r20, r26|->r23, r26|->r25, r27|->r1, r27|->r4, r27|->r9, r27|->r15, r27|->r16, r27|->r19, r27|->r20, r27|->r21, r27|->r24, r27|->r25, r28|->r1, r28|->r2, r28|->r4, r28|->r6, r28|->r7, r28|->r12, r28|->r13, r28|->r15, r28|->r17, r28|->r20, r28|->r21, r28|->r23, r28|->r24, r29|->r0, r29|->r1, r29|->r2, r29|->r6, r29|->r7, r29|->r8, r29|->r10, r29|->r12, r29|->r13, r29|->r14, r29|->r17, r29|->r19, r29|->r20, r29|->r21, r29|->r22, r29|->r24, r29|->r25, r29|->r26} &
    rules={rule0|->(rec(su:s3,re:r8,mo:per,pr: 4,co:{c1,c9,c0,c4})), rule1|->(rec(su:s26,re:r10,mo:per,pr: 1,co:{c0,c5,c2,c9})), rule2|->(rec(su:s17,re:r16,mo:per,pr: 2,co:{c4})), rule3|->(rec(su:s8,re:r6,mo:per,pr: 2,co:{c8,c1,c6,c0,c2})), rule4|->(rec(su:s9,re:r10,mo:pro,pr: 4,co:{c9,c4,c6,c0,c7,c1,c8})), rule5|->(rec(su:s27,re:r19,mo:per,pr: 3,co:{c6,c0,c5,c4,c7})), rule6|->(rec(su:s29,re:r23,mo:per,pr: 2,co:{c4,c8,c0})), rule7|->(rec(su:s1,re:r8,mo:per,pr: 0,co:{c7,c2,c9,c3,c6,c5})), rule8|->(rec(su:s22,re:r23,mo:pro,pr: 4,co:{c5,c4,c2,c0,c3})), rule9|->(rec(su:s4,re:r19,mo:pro,pr: 2,co:{c1,c4,c8})), rule10|->(rec(su:s15,re:r17,mo:per,pr: 4,co:{c8,c5,c2,c4,c1,c0})), rule11|->(rec(su:s28,re:r2,mo:pro,pr: 1,co:{c9,c7}))}

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