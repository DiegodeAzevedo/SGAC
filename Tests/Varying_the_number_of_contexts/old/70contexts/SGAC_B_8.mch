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
    e_sub={s3|->s0, s3|->s1, s3|->s2, s4|->s2, s5|->s1, s5|->s3, s6|->s0, s6|->s5, s7|->s0, s7|->s1, s7|->s5, s7|->s6, s8|->s0, s8|->s4, s8|->s6, s8|->s7, s9|->s2, s9|->s4, s9|->s7, s10|->s1, s10|->s5, s10|->s6, s10|->s7, s10|->s9, s11|->s2, s11|->s3, s11|->s4, s11|->s6, s11|->s8, s12|->s2, s12|->s4, s12|->s5, s12|->s6, s12|->s7, s12|->s8, s13|->s2, s13|->s6, s13|->s7, s13|->s10, s13|->s11, s14|->s0, s14|->s1, s14|->s2, s14|->s5, s14|->s6, s14|->s7, s14|->s9, s14|->s11, s14|->s12, s15|->s0, s15|->s1, s15|->s2, s15|->s3, s15|->s6, s15|->s7, s15|->s8, s15|->s9, s15|->s10, s15|->s11, s15|->s12, s15|->s14, s16|->s1, s16|->s6, s16|->s7, s16|->s8, s16|->s11, s16|->s12, s16|->s14, s16|->s15, s17|->s1, s17|->s2, s17|->s5, s17|->s7, s17|->s8, s17|->s10, s17|->s11, s17|->s12, s17|->s14, s17|->s16, s18|->s3, s18|->s7, s18|->s8, s18|->s9, s18|->s10, s18|->s11, s18|->s12, s18|->s13, s18|->s14, s18|->s15, s18|->s16, s19|->s0, s19|->s1, s19|->s2, s19|->s4, s19|->s5, s19|->s11, s19|->s14, s19|->s16, s19|->s17, s19|->s18, s20|->s0, s20|->s1, s20|->s3, s20|->s5, s20|->s9, s20|->s11, s20|->s16, s20|->s17, s21|->s0, s21|->s1, s21|->s3, s21|->s4, s21|->s5, s21|->s8, s21|->s9, s21|->s11, s21|->s13, s21|->s14, s21|->s16, s21|->s17, s21|->s19, s22|->s0, s22|->s1, s22|->s2, s22|->s3, s22|->s6, s22|->s7, s22|->s8, s22|->s10, s22|->s11, s22|->s12, s22|->s14, s22|->s16, s22|->s17, s22|->s18, s22|->s19, s23|->s1, s23|->s3, s23|->s5, s23|->s6, s23|->s8, s23|->s11, s23|->s13, s23|->s14, s23|->s15, s23|->s16, s23|->s17, s23|->s22, s24|->s0, s24|->s2, s24|->s7, s24|->s8, s24|->s9, s24|->s16, s24|->s17, s24|->s21, s24|->s23, s25|->s4, s25|->s5, s25|->s6, s25|->s7, s25|->s8, s25|->s9, s25|->s10, s25|->s12, s25|->s14, s25|->s18, s25|->s20, s25|->s21, s26|->s1, s26|->s2, s26|->s6, s26|->s9, s26|->s11, s26|->s13, s26|->s14, s26|->s16, s26|->s18, s26|->s19, s26|->s20, s26|->s25, s27|->s1, s27|->s3, s27|->s6, s27|->s7, s27|->s9, s27|->s12, s27|->s14, s27|->s17, s27|->s19, s27|->s20, s27|->s22, s27|->s25, s28|->s2, s28|->s3, s28|->s5, s28|->s7, s28|->s8, s28|->s12, s28|->s14, s28|->s17, s28|->s19, s28|->s21, s28|->s26, s29|->s2, s29|->s6, s29|->s7, s29|->s11, s29|->s12, s29|->s15, s29|->s16, s29|->s18, s29|->s19, s29|->s20, s29|->s24, s29|->s26, s29|->s27} &
    e_res={r2|->r0, r2|->r1, r3|->r1, r4|->r2, r4|->r3, r5|->r1, r5|->r4, r6|->r1, r6|->r3, r7|->r2, r8|->r0, r8|->r4, r8|->r5, r9|->r3, r9|->r4, r9|->r6, r10|->r0, r10|->r2, r10|->r4, r10|->r5, r10|->r6, r11|->r0, r11|->r1, r11|->r4, r11|->r5, r11|->r7, r11|->r8, r11|->r10, r12|->r0, r12|->r2, r12|->r3, r12|->r4, r12|->r5, r12|->r6, r12|->r7, r12|->r9, r13|->r2, r13|->r4, r13|->r5, r13|->r6, r13|->r10, r13|->r11, r14|->r0, r14|->r2, r14|->r3, r14|->r5, r14|->r7, r14|->r9, r14|->r12, r15|->r2, r15|->r6, r15|->r8, r15|->r9, r15|->r10, r15|->r11, r16|->r1, r16|->r3, r16|->r7, r16|->r8, r16|->r9, r16|->r10, r16|->r13, r16|->r15, r17|->r1, r17|->r3, r17|->r8, r17|->r11, r17|->r13, r17|->r15, r18|->r7, r18|->r14, r18|->r15, r19|->r2, r19|->r7, r19|->r8, r19|->r9, r19|->r10, r19|->r15, r19|->r16, r19|->r17, r19|->r18, r20|->r1, r20|->r5, r20|->r6, r20|->r10, r20|->r13, r20|->r16, r20|->r19, r21|->r0, r21|->r3, r21|->r9, r21|->r11, r21|->r12, r21|->r14, r21|->r15, r21|->r16, r21|->r19, r22|->r0, r22|->r4, r22|->r7, r22|->r12, r22|->r13, r23|->r0, r23|->r1, r23|->r2, r23|->r6, r23|->r7, r23|->r9, r23|->r12, r23|->r14, r23|->r16, r23|->r18, r23|->r21, r24|->r1, r24|->r2, r24|->r3, r24|->r6, r24|->r9, r24|->r11, r24|->r12, r24|->r14, r24|->r16, r24|->r20, r24|->r22, r25|->r3, r25|->r5, r25|->r8, r25|->r12, r25|->r13, r25|->r14, r25|->r15, r25|->r17, r25|->r18, r25|->r20, r25|->r22, r25|->r24, r26|->r0, r26|->r2, r26|->r3, r26|->r5, r26|->r6, r26|->r7, r26|->r8, r26|->r9, r26|->r10, r26|->r11, r26|->r14, r26|->r18, r26|->r20, r26|->r21, r26|->r23, r26|->r25, r27|->r1, r27|->r3, r27|->r4, r27|->r6, r27|->r8, r27|->r13, r27|->r15, r27|->r16, r27|->r24, r27|->r26, r28|->r0, r28|->r1, r28|->r3, r28|->r4, r28|->r6, r28|->r7, r28|->r14, r28|->r18, r28|->r19, r28|->r20, r28|->r21, r28|->r22, r28|->r23, r28|->r24, r28|->r25, r28|->r26, r29|->r2, r29|->r4, r29|->r5, r29|->r7, r29|->r8, r29|->r10, r29|->r12, r29|->r16, r29|->r21, r29|->r23, r29|->r24, r29|->r25, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s11,re:r2,mo:per,pr: 1,co:{c1,c9,c6})), rule1|->(rec(su:s13,re:r16,mo:pro,pr: 0,co:{c6,c8,c2})), rule2|->(rec(su:s6,re:r22,mo:pro,pr: 3,co:{c1,c5})), rule3|->(rec(su:s12,re:r21,mo:pro,pr: 0,co:{c9,c5,c8,c4,c0})), rule4|->(rec(su:s0,re:r16,mo:per,pr: 2,co:{c5,c1,c6,c4,c7})), rule5|->(rec(su:s26,re:r18,mo:per,pr: 3,co:{c5,c1,c2})), rule6|->(rec(su:s23,re:r24,mo:pro,pr: 3,co:{c9,c2,c8,c0})), rule7|->(rec(su:s13,re:r25,mo:pro,pr: 4,co:{c7})), rule8|->(rec(su:s18,re:r0,mo:per,pr: 0,co:{c6})), rule9|->(rec(su:s3,re:r6,mo:pro,pr: 4,co:{c7,c4,c6,c9,c8})), rule10|->(rec(su:s11,re:r10,mo:pro,pr: 0,co:{c9,c3,c0})), rule11|->(rec(su:s21,re:r20,mo:pro,pr: 0,co:{c4,c6,c1,c3,c5,c0,c7}))}

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