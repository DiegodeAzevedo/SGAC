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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s3|->s1, s4|->s0, s4|->s1, s4|->s2, s5|->s2, s5|->s3, s6|->s1, s6|->s4, s7|->s1, s7|->s3, s8|->s0, s8|->s1, s8|->s3, s8|->s5, s8|->s7, s9|->s1, s9|->s3, s9|->s4, s9|->s5, s9|->s6, s9|->s7, s10|->s0, s10|->s1, s10|->s2, s10|->s3, s10|->s5, s10|->s9, s11|->s0, s11|->s2, s11|->s4, s11|->s6, s11|->s8, s11|->s10, s12|->s1, s12|->s2, s12|->s4, s12|->s5, s12|->s6, s12|->s7, s12|->s9, s13|->s5, s13|->s7, s13|->s8, s13|->s9, s13|->s10, s13|->s11, s13|->s12, s14|->s0, s14|->s4, s14|->s5, s14|->s6, s14|->s7, s14|->s9, s14|->s10, s14|->s11, s14|->s12, s14|->s13, s15|->s0, s15|->s1, s15|->s4, s15|->s6, s15|->s7, s15|->s10, s15|->s11, s15|->s14, s16|->s1, s16|->s2, s16|->s4, s16|->s10, s16|->s12, s16|->s13, s17|->s0, s17|->s4, s17|->s6, s17|->s12, s17|->s13, s17|->s14, s17|->s16, s18|->s0, s18|->s4, s18|->s6, s18|->s7, s18|->s10, s18|->s14, s18|->s15, s19|->s0, s19|->s3, s19|->s8, s19|->s9, s19|->s10, s19|->s11, s19|->s12, s19|->s17, s19|->s18, s20|->s2, s20|->s8, s20|->s9, s20|->s11, s20|->s12, s20|->s13, s20|->s14, s20|->s16, s20|->s17, s20|->s18, s20|->s19, s21|->s3, s21|->s5, s21|->s6, s21|->s7, s21|->s9, s21|->s10, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s15, s21|->s16, s21|->s17, s21|->s20, s22|->s1, s22|->s6, s22|->s7, s22|->s8, s22|->s9, s22|->s10, s22|->s11, s22|->s14, s22|->s20, s23|->s0, s23|->s1, s23|->s3, s23|->s7, s23|->s8, s23|->s9, s23|->s11, s23|->s13, s23|->s14, s23|->s16, s23|->s17, s23|->s18, s23|->s22, s24|->s4, s24|->s6, s24|->s9, s24|->s10, s24|->s12, s24|->s17, s24|->s19, s24|->s22, s24|->s23, s25|->s0, s25|->s2, s25|->s4, s25|->s6, s25|->s7, s25|->s9, s25|->s12, s25|->s13, s25|->s14, s25|->s15, s25|->s16, s25|->s17, s25|->s18, s25|->s20, s25|->s23, s25|->s24, s26|->s0, s26|->s1, s26|->s4, s26|->s5, s26|->s6, s26|->s8, s26|->s11, s26|->s12, s26|->s13, s26|->s14, s26|->s15, s26|->s17, s26|->s18, s26|->s19, s26|->s20, s26|->s21, s26|->s25, s27|->s1, s27|->s2, s27|->s3, s27|->s5, s27|->s8, s27|->s9, s27|->s11, s27|->s14, s27|->s15, s27|->s17, s27|->s18, s27|->s19, s27|->s21, s27|->s25, s27|->s26, s28|->s2, s28|->s4, s28|->s7, s28|->s8, s28|->s9, s28|->s10, s28|->s11, s28|->s14, s28|->s16, s28|->s17, s28|->s20, s28|->s22, s28|->s24, s29|->s0, s29|->s1, s29|->s3, s29|->s8, s29|->s10, s29|->s14, s29|->s15, s29|->s16, s29|->s17, s29|->s19, s29|->s20, s29|->s21, s29|->s25} &
    e_res={r2|->r1, r3|->r2, r4|->r1, r4|->r2, r4|->r3, r5|->r0, r6|->r1, r6|->r2, r6|->r3, r6|->r4, r6|->r5, r7|->r2, r7|->r6, r8|->r1, r8|->r5, r8|->r6, r8|->r7, r9|->r2, r9|->r3, r9|->r4, r9|->r5, r9|->r8, r10|->r0, r10|->r2, r10|->r3, r10|->r4, r10|->r5, r10|->r6, r11|->r1, r11|->r3, r11|->r4, r11|->r5, r11|->r7, r11|->r10, r12|->r2, r12|->r3, r12|->r5, r12|->r6, r12|->r7, r12|->r8, r12|->r9, r13|->r1, r13|->r5, r13|->r6, r13|->r7, r13|->r12, r14|->r0, r14|->r1, r14|->r3, r14|->r5, r14|->r8, r14|->r9, r14|->r10, r14|->r12, r15|->r1, r15|->r3, r15|->r4, r15|->r5, r15|->r6, r15|->r7, r15|->r10, r15|->r12, r15|->r14, r16|->r0, r16|->r1, r16|->r2, r16|->r5, r16|->r7, r16|->r9, r16|->r10, r16|->r12, r16|->r13, r16|->r15, r17|->r0, r17|->r3, r17|->r4, r17|->r10, r17|->r11, r17|->r14, r17|->r15, r18|->r4, r18|->r5, r18|->r7, r18|->r8, r18|->r10, r18|->r12, r18|->r17, r19|->r2, r19|->r7, r19|->r9, r19|->r10, r19|->r11, r19|->r13, r19|->r16, r19|->r17, r20|->r1, r20|->r4, r20|->r7, r20|->r17, r21|->r0, r21|->r1, r21|->r4, r21|->r5, r21|->r7, r21|->r12, r21|->r13, r21|->r14, r21|->r17, r21|->r18, r21|->r19, r21|->r20, r22|->r3, r22|->r4, r22|->r6, r22|->r8, r22|->r9, r22|->r10, r22|->r11, r22|->r14, r22|->r15, r22|->r16, r22|->r17, r22|->r19, r22|->r21, r23|->r0, r23|->r1, r23|->r3, r23|->r5, r23|->r10, r23|->r13, r23|->r15, r23|->r16, r23|->r17, r23|->r18, r24|->r5, r24|->r10, r24|->r12, r24|->r14, r24|->r15, r24|->r18, r24|->r20, r24|->r22, r24|->r23, r25|->r1, r25|->r5, r25|->r6, r25|->r7, r25|->r9, r25|->r12, r25|->r14, r25|->r15, r25|->r16, r25|->r17, r25|->r18, r25|->r20, r25|->r22, r26|->r0, r26|->r1, r26|->r4, r26|->r5, r26|->r7, r26|->r11, r26|->r13, r26|->r14, r26|->r15, r26|->r17, r26|->r19, r26|->r20, r26|->r22, r26|->r23, r26|->r24, r27|->r0, r27|->r5, r27|->r7, r27|->r11, r27|->r12, r27|->r13, r27|->r15, r27|->r17, r27|->r18, r27|->r20, r27|->r24, r27|->r25, r28|->r2, r28|->r5, r28|->r9, r28|->r10, r28|->r12, r28|->r13, r28|->r18, r28|->r19, r28|->r20, r28|->r22, r28|->r24, r29|->r0, r29|->r3, r29|->r6, r29|->r8, r29|->r9, r29|->r10, r29|->r11, r29|->r12, r29|->r14, r29|->r16, r29|->r21, r29|->r22, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s11,re:r15,mo:pro,pr: 3,co:{c3,c4,c9,c7,c8})), rule1|->(rec(su:s21,re:r28,mo:per,pr: 4,co:{c1})), rule2|->(rec(su:s24,re:r16,mo:pro,pr: 1,co:{c3,c1,c5,c4,c0})), rule3|->(rec(su:s18,re:r14,mo:pro,pr: 1,co:{c0,c9,c6,c4,c5,c3})), rule4|->(rec(su:s9,re:r28,mo:pro,pr: 1,co:{c6,c2,c5,c7})), rule5|->(rec(su:s10,re:r26,mo:per,pr: 4,co:{c8,c7,c2})), rule6|->(rec(su:s2,re:r22,mo:pro,pr: 3,co:{c7,c5})), rule7|->(rec(su:s11,re:r11,mo:per,pr: 4,co:{c2,c6,c0,c4})), rule8|->(rec(su:s12,re:r14,mo:pro,pr: 2,co:{c2,c4})), rule9|->(rec(su:s12,re:r3,mo:pro,pr: 1,co:{c0,c8,c1})), rule10|->(rec(su:s10,re:r27,mo:per,pr: 4,co:{c9})), rule11|->(rec(su:s16,re:r13,mo:pro,pr: 0,co:{c8,c5,c7,c6,c0,c2}))}

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