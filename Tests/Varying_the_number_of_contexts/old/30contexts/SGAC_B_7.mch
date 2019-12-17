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
    e_sub={s2|->s1, s3|->s0, s3|->s2, s4|->s0, s4|->s1, s4|->s2, s4|->s3, s5|->s0, s5|->s1, s5|->s2, s5|->s3, s6|->s0, s6|->s2, s6|->s3, s7|->s0, s7|->s2, s7|->s3, s7|->s4, s7|->s5, s7|->s6, s8|->s1, s8|->s2, s8|->s4, s8|->s5, s8|->s6, s9|->s0, s9|->s1, s9|->s3, s9|->s4, s9|->s6, s9|->s7, s10|->s0, s10|->s1, s10|->s2, s10|->s6, s10|->s7, s10|->s9, s11|->s3, s11|->s4, s11|->s5, s11|->s10, s12|->s0, s12|->s4, s12|->s6, s12|->s7, s12|->s8, s12|->s9, s13|->s1, s13|->s4, s13|->s5, s13|->s10, s13|->s12, s14|->s1, s14|->s3, s14|->s9, s15|->s0, s15|->s2, s15|->s3, s15|->s4, s15|->s6, s15|->s8, s15|->s12, s15|->s13, s16|->s0, s16|->s1, s16|->s2, s16|->s9, s16|->s10, s16|->s11, s16|->s12, s16|->s15, s17|->s2, s17|->s3, s17|->s6, s17|->s9, s17|->s12, s17|->s13, s18|->s0, s18|->s1, s18|->s13, s18|->s16, s19|->s0, s19|->s1, s19|->s2, s19|->s4, s19|->s5, s19|->s6, s19|->s8, s19|->s9, s19|->s11, s19|->s15, s19|->s18, s20|->s1, s20|->s2, s20|->s3, s20|->s5, s20|->s8, s20|->s9, s20|->s13, s20|->s14, s20|->s17, s21|->s0, s21|->s1, s21|->s2, s21|->s3, s21|->s4, s21|->s5, s21|->s7, s21|->s8, s21|->s10, s21|->s15, s21|->s16, s21|->s17, s21|->s18, s22|->s0, s22|->s5, s22|->s6, s22|->s11, s22|->s12, s22|->s13, s22|->s15, s22|->s16, s22|->s19, s22|->s20, s22|->s21, s23|->s0, s23|->s1, s23|->s2, s23|->s6, s23|->s7, s23|->s10, s23|->s11, s23|->s12, s23|->s15, s23|->s19, s23|->s20, s23|->s21, s24|->s0, s24|->s2, s24|->s5, s24|->s6, s24|->s7, s24|->s9, s24|->s12, s24|->s13, s24|->s19, s24|->s23, s25|->s3, s25|->s6, s25|->s7, s25|->s9, s25|->s10, s25|->s12, s25|->s14, s25|->s16, s25|->s17, s25|->s18, s25|->s19, s26|->s0, s26|->s2, s26|->s6, s26|->s8, s26|->s11, s26|->s12, s26|->s13, s26|->s15, s26|->s21, s26|->s22, s26|->s23, s26|->s24, s26|->s25, s27|->s1, s27|->s2, s27|->s4, s27|->s9, s27|->s10, s27|->s12, s27|->s14, s27|->s15, s27|->s16, s27|->s21, s27|->s25, s27|->s26, s28|->s1, s28|->s3, s28|->s6, s28|->s9, s28|->s12, s28|->s14, s28|->s15, s28|->s19, s28|->s20, s28|->s22, s28|->s24, s28|->s27, s29|->s1, s29|->s2, s29|->s5, s29|->s6, s29|->s8, s29|->s9, s29|->s10, s29|->s15, s29|->s19, s29|->s22} &
    e_res={r1|->r0, r2|->r0, r3|->r2, r4|->r0, r4|->r1, r5|->r3, r5|->r4, r6|->r0, r6|->r1, r6|->r3, r6|->r5, r7|->r2, r7|->r3, r7|->r4, r8|->r0, r8|->r3, r9|->r1, r9|->r3, r9|->r4, r9|->r6, r9|->r7, r9|->r8, r10|->r0, r10|->r2, r10|->r4, r10|->r6, r10|->r8, r11|->r1, r11|->r2, r11|->r4, r11|->r5, r11|->r6, r11|->r9, r11|->r10, r12|->r0, r12|->r3, r12|->r4, r12|->r5, r12|->r6, r12|->r10, r12|->r11, r13|->r0, r13|->r2, r13|->r3, r13|->r8, r13|->r9, r13|->r12, r14|->r0, r14|->r3, r14|->r6, r14|->r8, r14|->r9, r14|->r11, r14|->r13, r15|->r1, r15|->r3, r15|->r4, r15|->r5, r15|->r6, r15|->r9, r15|->r12, r15|->r14, r16|->r0, r16|->r1, r16|->r2, r16|->r3, r16|->r4, r16|->r6, r16|->r9, r16|->r15, r17|->r1, r17|->r2, r17|->r3, r17|->r4, r17|->r7, r17|->r9, r17|->r10, r17|->r12, r17|->r13, r18|->r0, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r9, r18|->r13, r18|->r17, r19|->r1, r19|->r3, r19|->r4, r19|->r8, r19|->r9, r19|->r10, r19|->r11, r19|->r12, r19|->r14, r19|->r15, r19|->r16, r20|->r0, r20|->r2, r20|->r3, r20|->r7, r20|->r9, r20|->r13, r20|->r16, r20|->r18, r20|->r19, r21|->r0, r21|->r2, r21|->r4, r21|->r5, r21|->r10, r21|->r12, r21|->r14, r21|->r15, r21|->r16, r22|->r2, r22|->r6, r22|->r7, r22|->r9, r22|->r11, r22|->r15, r22|->r17, r22|->r20, r22|->r21, r23|->r0, r23|->r1, r23|->r5, r23|->r9, r23|->r13, r23|->r17, r23|->r18, r23|->r19, r23|->r21, r24|->r0, r24|->r1, r24|->r2, r24|->r3, r24|->r4, r24|->r6, r24|->r9, r24|->r10, r24|->r11, r24|->r13, r24|->r19, r24|->r21, r25|->r0, r25|->r2, r25|->r3, r25|->r4, r25|->r6, r25|->r11, r25|->r18, r25|->r19, r25|->r20, r25|->r21, r25|->r23, r25|->r24, r26|->r0, r26|->r1, r26|->r5, r26|->r7, r26|->r10, r26|->r13, r26|->r15, r26|->r17, r26|->r18, r26|->r19, r26|->r21, r27|->r2, r27|->r3, r27|->r4, r27|->r6, r27|->r7, r27|->r9, r27|->r11, r27|->r12, r27|->r13, r27|->r15, r27|->r16, r27|->r17, r27|->r20, r27|->r22, r27|->r23, r27|->r24, r27|->r26, r28|->r0, r28|->r1, r28|->r4, r28|->r5, r28|->r6, r28|->r7, r28|->r8, r28|->r9, r28|->r10, r28|->r12, r28|->r13, r28|->r14, r28|->r16, r28|->r18, r28|->r20, r28|->r24, r28|->r26, r29|->r0, r29|->r1, r29|->r2, r29|->r6, r29|->r7, r29|->r11, r29|->r14, r29|->r16, r29|->r21, r29|->r22, r29|->r23, r29|->r24, r29|->r25, r29|->r26, r29|->r28} &
    rules={rule0|->(rec(su:s3,re:r29,mo:per,pr: 3,co:{c6,c5,c0})), rule1|->(rec(su:s9,re:r18,mo:pro,pr: 3,co:{c2,c5,c7,c0,c1,c4})), rule2|->(rec(su:s7,re:r27,mo:per,pr: 4,co:{c2,c0,c1})), rule3|->(rec(su:s23,re:r9,mo:per,pr: 0,co:{c4,c6})), rule4|->(rec(su:s14,re:r26,mo:pro,pr: 4,co:{c8,c5,c4})), rule5|->(rec(su:s3,re:r1,mo:pro,pr: 2,co:{c6,c2,c3})), rule6|->(rec(su:s0,re:r11,mo:pro,pr: 0,co:{c7,c1,c5})), rule7|->(rec(su:s19,re:r7,mo:per,pr: 2,co:{c9,c3,c5,c0})), rule8|->(rec(su:s11,re:r29,mo:pro,pr: 2,co:{c3,c5,c7,c2,c4,c9,c8})), rule9|->(rec(su:s21,re:r21,mo:per,pr: 3,co:{c3,c6,c1,c2})), rule10|->(rec(su:s17,re:r19,mo:per,pr: 3,co:{c5,c7,c6,c9,c3,c4})), rule11|->(rec(su:s8,re:r28,mo:per,pr: 1,co:{c2,c0,c5,c9,c8,c7,c3}))}

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