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
    e_sub={s1|->s0, s2|->s0, s3|->s0, s3|->s1, s4|->s0, s4|->s1, s4|->s2, s4|->s3, s5|->s3, s6|->s0, s6|->s1, s6|->s2, s6|->s4, s6|->s5, s7|->s0, s7|->s2, s7|->s3, s7|->s4, s7|->s5, s8|->s0, s8|->s2, s8|->s4, s8|->s7, s9|->s0, s9|->s3, s9|->s6, s9|->s7, s9|->s8, s10|->s0, s10|->s1, s10|->s2, s10|->s4, s10|->s8, s10|->s9, s11|->s1, s11|->s3, s11|->s4, s11|->s6, s11|->s8, s11|->s10, s12|->s3, s12|->s7, s12|->s9, s13|->s1, s13|->s2, s13|->s3, s13|->s4, s13|->s7, s13|->s8, s13|->s10, s14|->s0, s14|->s1, s14|->s2, s14|->s3, s14|->s4, s14|->s5, s14|->s6, s14|->s8, s14|->s9, s14|->s12, s14|->s13, s15|->s1, s15|->s3, s15|->s5, s15|->s6, s15|->s8, s15|->s10, s15|->s11, s15|->s12, s15|->s14, s16|->s0, s16|->s3, s16|->s4, s16|->s9, s16|->s12, s16|->s15, s17|->s0, s17|->s2, s17|->s3, s17|->s4, s17|->s5, s17|->s9, s17|->s11, s17|->s14, s18|->s0, s18|->s2, s18|->s9, s18|->s11, s18|->s12, s18|->s13, s18|->s14, s18|->s15, s18|->s16, s19|->s0, s19|->s1, s19|->s2, s19|->s3, s19|->s6, s19|->s7, s19|->s10, s19|->s11, s19|->s13, s19|->s15, s20|->s0, s20|->s1, s20|->s2, s20|->s4, s20|->s5, s20|->s8, s20|->s13, s20|->s14, s20|->s15, s20|->s16, s20|->s17, s20|->s19, s21|->s0, s21|->s2, s21|->s3, s21|->s5, s21|->s7, s21|->s10, s21|->s13, s21|->s14, s21|->s15, s21|->s16, s21|->s20, s22|->s0, s22|->s1, s22|->s2, s22|->s4, s22|->s8, s22|->s10, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s17, s22|->s18, s22|->s19, s23|->s0, s23|->s2, s23|->s3, s23|->s4, s23|->s5, s23|->s13, s23|->s14, s23|->s15, s23|->s18, s24|->s1, s24|->s2, s24|->s3, s24|->s10, s24|->s13, s24|->s14, s24|->s15, s24|->s17, s24|->s19, s24|->s21, s24|->s23, s25|->s0, s25|->s1, s25|->s2, s25|->s7, s25|->s8, s25|->s10, s25|->s11, s25|->s13, s25|->s15, s25|->s23, s25|->s24, s26|->s0, s26|->s8, s26|->s11, s26|->s16, s26|->s18, s26|->s20, s26|->s21, s26|->s23, s26|->s25, s27|->s1, s27|->s3, s27|->s4, s27|->s5, s27|->s6, s27|->s7, s27|->s10, s27|->s11, s27|->s12, s27|->s15, s27|->s21, s27|->s22, s27|->s23, s27|->s26, s28|->s0, s28|->s1, s28|->s2, s28|->s6, s28|->s7, s28|->s9, s28|->s12, s28|->s15, s28|->s16, s28|->s20, s28|->s21, s28|->s22, s28|->s25, s28|->s26, s29|->s1, s29|->s3, s29|->s4, s29|->s5, s29|->s8, s29|->s15, s29|->s17, s29|->s18, s29|->s19, s29|->s22, s29|->s25, s29|->s26, s29|->s27} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r3|->r0, r3|->r2, r4|->r3, r5|->r1, r6|->r0, r6|->r2, r7|->r2, r7|->r6, r8|->r2, r8|->r4, r8|->r6, r8|->r7, r9|->r1, r9|->r3, r9|->r4, r9|->r8, r10|->r2, r10|->r4, r10|->r6, r10|->r7, r10|->r8, r11|->r0, r11|->r1, r11|->r3, r11|->r9, r11|->r10, r12|->r0, r12|->r1, r12|->r2, r12|->r5, r12|->r6, r12|->r10, r12|->r11, r13|->r0, r13|->r1, r13|->r5, r13|->r6, r13|->r7, r13|->r10, r13|->r11, r14|->r0, r14|->r1, r14|->r2, r14|->r5, r14|->r6, r14|->r7, r14|->r8, r14|->r11, r14|->r12, r14|->r13, r15|->r0, r15|->r1, r15|->r2, r15|->r6, r15|->r8, r15|->r9, r15|->r10, r15|->r12, r16|->r6, r16|->r7, r16|->r9, r16|->r12, r16|->r13, r16|->r14, r17|->r0, r17|->r1, r17|->r3, r17|->r5, r17|->r8, r17|->r12, r17|->r16, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r9, r18|->r11, r18|->r17, r19|->r1, r19|->r2, r19|->r7, r19|->r9, r19|->r10, r19|->r11, r19|->r12, r19|->r14, r19|->r16, r20|->r0, r20|->r1, r20|->r3, r20|->r5, r20|->r8, r20|->r10, r20|->r13, r20|->r15, r20|->r16, r20|->r17, r20|->r18, r20|->r19, r21|->r0, r21|->r1, r21|->r3, r21|->r5, r21|->r6, r21|->r9, r21|->r10, r21|->r13, r21|->r16, r21|->r17, r21|->r20, r22|->r0, r22|->r4, r22|->r6, r22|->r9, r22|->r10, r22|->r11, r22|->r13, r22|->r16, r22|->r19, r22|->r20, r22|->r21, r23|->r3, r23|->r4, r23|->r7, r23|->r11, r23|->r12, r23|->r13, r23|->r16, r23|->r18, r23|->r21, r24|->r0, r24|->r1, r24|->r2, r24|->r3, r24|->r4, r24|->r5, r24|->r7, r24|->r8, r24|->r10, r24|->r11, r24|->r13, r24|->r17, r24|->r19, r25|->r1, r25|->r2, r25|->r3, r25|->r4, r25|->r10, r25|->r11, r25|->r12, r25|->r15, r25|->r19, r25|->r20, r25|->r21, r25|->r22, r26|->r0, r26|->r2, r26|->r3, r26|->r5, r26|->r7, r26|->r8, r26|->r10, r26|->r11, r26|->r12, r26|->r15, r26|->r17, r26|->r19, r26|->r23, r26|->r25, r27|->r2, r27|->r4, r27|->r5, r27|->r7, r27|->r12, r27|->r14, r27|->r15, r27|->r16, r27|->r17, r28|->r1, r28|->r2, r28|->r3, r28|->r5, r28|->r6, r28|->r7, r28|->r8, r28|->r9, r28|->r10, r28|->r11, r28|->r13, r28|->r14, r28|->r15, r28|->r18, r28|->r19, r28|->r23, r28|->r24, r28|->r27, r29|->r3, r29|->r4, r29|->r10, r29|->r11, r29|->r12, r29|->r13, r29|->r16, r29|->r17, r29|->r18, r29|->r19, r29|->r21, r29|->r23, r29|->r26} &
    rules={rule0|->(rec(su:s17,re:r20,mo:per,pr: 4,co:{c4,c1,c9,c6,c0,c5})), rule1|->(rec(su:s16,re:r18,mo:pro,pr: 3,co:{c0,c9,c4,c1})), rule2|->(rec(su:s27,re:r29,mo:per,pr: 3,co:{c2,c4,c6,c7,c1})), rule3|->(rec(su:s10,re:r8,mo:per,pr: 3,co:{c3,c1,c9,c7,c4})), rule4|->(rec(su:s20,re:r18,mo:pro,pr: 4,co:{c0,c3,c6,c1,c7})), rule5|->(rec(su:s6,re:r13,mo:pro,pr: 1,co:{c1,c3,c4,c2,c8,c7})), rule6|->(rec(su:s14,re:r29,mo:per,pr: 3,co:{c5,c0,c7,c8,c4,c9})), rule7|->(rec(su:s5,re:r11,mo:pro,pr: 0,co:{c1,c7,c4,c5,c6,c3,c8})), rule8|->(rec(su:s13,re:r16,mo:pro,pr: 2,co:{c1,c4,c3,c6,c2,c5,c8})), rule9|->(rec(su:s13,re:r11,mo:pro,pr: 3,co:{c9,c3,c0,c4})), rule10|->(rec(su:s17,re:r2,mo:pro,pr: 3,co:{c5,c8})), rule11|->(rec(su:s22,re:r16,mo:per,pr: 4,co:{c4,c0,c9}))}

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