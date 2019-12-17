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
    e_sub={s3|->s0, s3|->s1, s3|->s2, s4|->s0, s4|->s1, s4|->s2, s4|->s3, s5|->s4, s6|->s0, s6|->s2, s6|->s3, s7|->s0, s7|->s2, s7|->s3, s8|->s0, s8|->s2, s8|->s3, s8|->s4, s8|->s5, s9|->s0, s9|->s1, s9|->s2, s9|->s4, s9|->s6, s9|->s7, s9|->s8, s10|->s1, s10|->s2, s10|->s6, s10|->s8, s11|->s0, s11|->s3, s11|->s5, s11|->s6, s11|->s7, s11|->s9, s11|->s10, s12|->s0, s12|->s1, s12|->s2, s12|->s4, s12|->s8, s12|->s10, s13|->s0, s13|->s2, s13|->s5, s13|->s6, s13|->s9, s13|->s11, s14|->s0, s14|->s3, s14|->s4, s14|->s5, s14|->s6, s14|->s7, s14|->s8, s14|->s9, s14|->s10, s14|->s12, s15|->s0, s15|->s1, s15|->s3, s15|->s6, s15|->s7, s15|->s8, s15|->s10, s15|->s11, s15|->s13, s15|->s14, s16|->s0, s16|->s2, s16|->s9, s16|->s12, s16|->s13, s16|->s15, s17|->s1, s17|->s6, s17|->s9, s17|->s10, s17|->s11, s18|->s1, s18|->s4, s18|->s8, s18|->s9, s18|->s10, s18|->s13, s18|->s16, s19|->s0, s19|->s1, s19|->s4, s19|->s5, s19|->s6, s19|->s11, s19|->s12, s19|->s14, s19|->s15, s19|->s16, s19|->s17, s20|->s2, s20|->s3, s20|->s5, s20|->s6, s20|->s7, s20|->s10, s20|->s11, s20|->s12, s20|->s16, s20|->s19, s21|->s0, s21|->s1, s21|->s2, s21|->s7, s21|->s8, s21|->s12, s21|->s13, s21|->s14, s21|->s15, s21|->s16, s21|->s18, s21|->s19, s22|->s1, s22|->s6, s22|->s9, s22|->s10, s22|->s12, s22|->s13, s22|->s15, s22|->s16, s22|->s17, s22|->s20, s23|->s0, s23|->s3, s23|->s5, s23|->s7, s23|->s9, s23|->s10, s23|->s12, s23|->s14, s23|->s15, s23|->s16, s23|->s17, s23|->s19, s23|->s20, s24|->s1, s24|->s6, s24|->s7, s24|->s9, s24|->s10, s24|->s11, s24|->s12, s24|->s14, s24|->s15, s24|->s18, s24|->s20, s24|->s22, s24|->s23, s25|->s0, s25|->s2, s25|->s3, s25|->s5, s25|->s9, s25|->s12, s25|->s17, s25|->s18, s25|->s20, s25|->s22, s25|->s24, s26|->s2, s26|->s5, s26|->s7, s26|->s9, s26|->s12, s26|->s13, s26|->s15, s26|->s18, s26|->s20, s26|->s21, s26|->s22, s26|->s23, s26|->s24, s27|->s0, s27|->s1, s27|->s2, s27|->s7, s27|->s10, s27|->s11, s27|->s13, s27|->s14, s27|->s15, s27|->s16, s27|->s18, s27|->s20, s27|->s24, s27|->s25, s27|->s26, s28|->s2, s28|->s5, s28|->s8, s28|->s10, s28|->s12, s28|->s15, s28|->s16, s28|->s21, s28|->s22, s28|->s24, s28|->s26, s28|->s27, s29|->s2, s29|->s6, s29|->s8, s29|->s10, s29|->s16, s29|->s17, s29|->s19, s29|->s20, s29|->s22, s29|->s24} &
    e_res={r2|->r0, r2|->r1, r3|->r0, r4|->r0, r4|->r2, r5|->r0, r5|->r1, r5|->r3, r6|->r0, r6|->r1, r6|->r5, r7|->r0, r7|->r1, r7|->r3, r8|->r0, r8|->r4, r9|->r0, r9|->r3, r9|->r4, r9|->r6, r10|->r4, r10|->r5, r10|->r9, r11|->r0, r11|->r1, r11|->r3, r11|->r4, r11|->r7, r11|->r8, r11|->r10, r12|->r2, r12|->r5, r12|->r6, r12|->r8, r12|->r9, r13|->r0, r13|->r2, r13|->r3, r13|->r4, r13|->r5, r13|->r7, r13|->r10, r13|->r11, r14|->r1, r14|->r6, r14|->r7, r14|->r9, r14|->r10, r15|->r0, r15|->r2, r15|->r4, r15|->r5, r15|->r6, r15|->r8, r15|->r9, r15|->r11, r15|->r13, r16|->r0, r16|->r1, r16|->r3, r16|->r4, r16|->r7, r16|->r11, r16|->r12, r16|->r13, r16|->r15, r17|->r0, r17|->r1, r17|->r3, r17|->r6, r17|->r9, r17|->r12, r17|->r15, r17|->r16, r18|->r0, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r7, r18|->r9, r18|->r11, r18|->r12, r18|->r13, r18|->r17, r19|->r0, r19|->r1, r19|->r4, r19|->r10, r19|->r11, r19|->r12, r19|->r13, r19|->r15, r19|->r17, r20|->r0, r20|->r1, r20|->r3, r20|->r4, r20|->r5, r20|->r9, r20|->r11, r20|->r14, r20|->r15, r20|->r17, r21|->r0, r21|->r1, r21|->r4, r21|->r5, r21|->r6, r21|->r9, r21|->r11, r21|->r12, r21|->r13, r21|->r16, r21|->r19, r21|->r20, r22|->r1, r22|->r5, r22|->r6, r22|->r7, r22|->r8, r22|->r11, r22|->r17, r22|->r21, r23|->r2, r23|->r4, r23|->r7, r23|->r10, r23|->r11, r23|->r13, r23|->r14, r23|->r15, r23|->r16, r23|->r20, r23|->r21, r23|->r22, r24|->r0, r24|->r1, r24|->r3, r24|->r4, r24|->r6, r24|->r7, r24|->r8, r24|->r9, r24|->r13, r24|->r14, r24|->r15, r24|->r16, r24|->r17, r24|->r18, r24|->r19, r24|->r23, r25|->r0, r25|->r1, r25|->r2, r25|->r6, r25|->r7, r25|->r9, r25|->r11, r25|->r12, r25|->r14, r25|->r15, r25|->r17, r25|->r19, r25|->r20, r26|->r0, r26|->r1, r26|->r3, r26|->r6, r26|->r8, r26|->r9, r26|->r12, r26|->r15, r26|->r20, r26|->r21, r26|->r22, r26|->r24, r27|->r0, r27|->r3, r27|->r5, r27|->r16, r27|->r17, r27|->r20, r27|->r21, r27|->r22, r27|->r25, r27|->r26, r28|->r0, r28|->r1, r28|->r2, r28|->r4, r28|->r5, r28|->r6, r28|->r8, r28|->r9, r28|->r10, r28|->r11, r28|->r13, r28|->r14, r28|->r16, r28|->r17, r28|->r19, r28|->r20, r28|->r24, r28|->r25, r29|->r0, r29|->r3, r29|->r5, r29|->r6, r29|->r8, r29|->r9, r29|->r10, r29|->r11, r29|->r14, r29|->r15, r29|->r18, r29|->r22, r29|->r24, r29|->r27, r29|->r28} &
    rules={rule0|->(rec(su:s3,re:r25,mo:pro,pr: 4,co:{c0,c1,c4,c8,c9,c6,c5})), rule1|->(rec(su:s24,re:r29,mo:pro,pr: 1,co:{c8,c2,c6,c0,c9})), rule2|->(rec(su:s25,re:r13,mo:per,pr: 3,co:{c5,c7,c3,c0})), rule3|->(rec(su:s5,re:r5,mo:per,pr: 4,co:{c1,c7,c8,c6})), rule4|->(rec(su:s16,re:r17,mo:pro,pr: 3,co:{c2,c3,c6,c9,c4,c1})), rule5|->(rec(su:s0,re:r13,mo:per,pr: 0,co:{c1,c2,c6,c7,c0,c5,c8})), rule6|->(rec(su:s22,re:r26,mo:per,pr: 3,co:{c6,c1,c2,c7})), rule7|->(rec(su:s11,re:r21,mo:per,pr: 4,co:{c7,c0,c4,c6,c8,c9,c1,c2})), rule8|->(rec(su:s26,re:r11,mo:per,pr: 2,co:{c2,c1,c4,c9,c7})), rule9|->(rec(su:s15,re:r9,mo:pro,pr: 3,co:{c5})), rule10|->(rec(su:s19,re:r2,mo:pro,pr: 3,co:{c7,c2,c3,c6,c9})), rule11|->(rec(su:s12,re:r17,mo:per,pr: 1,co:{c4,c8}))}

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