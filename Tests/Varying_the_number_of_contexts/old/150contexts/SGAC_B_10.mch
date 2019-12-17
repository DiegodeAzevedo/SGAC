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
    e_sub={s2|->s1, s4|->s2, s5|->s0, s5|->s2, s6|->s0, s6|->s2, s6|->s4, s6|->s5, s7|->s0, s7|->s2, s7|->s4, s7|->s6, s8|->s2, s9|->s0, s9|->s3, s9|->s5, s9|->s7, s10|->s0, s10|->s2, s10|->s4, s10|->s5, s10|->s7, s10|->s9, s11|->s0, s11|->s1, s11|->s2, s11|->s3, s11|->s4, s11|->s7, s11|->s8, s11|->s9, s12|->s0, s12|->s2, s12|->s3, s12|->s5, s12|->s7, s12|->s8, s12|->s10, s13|->s0, s13|->s2, s13|->s4, s13|->s8, s13|->s9, s13|->s11, s13|->s12, s14|->s2, s14|->s3, s14|->s4, s14|->s6, s14|->s7, s14|->s10, s15|->s2, s15|->s3, s15|->s5, s15|->s6, s15|->s7, s15|->s9, s15|->s10, s16|->s1, s16|->s4, s16|->s5, s16|->s6, s16|->s8, s16|->s10, s16|->s11, s16|->s15, s17|->s0, s17|->s1, s17|->s2, s17|->s3, s17|->s5, s17|->s6, s17|->s7, s17|->s11, s17|->s12, s17|->s14, s17|->s15, s17|->s16, s18|->s1, s18|->s5, s18|->s7, s18|->s8, s18|->s17, s19|->s1, s19|->s3, s19|->s8, s19|->s9, s19|->s10, s19|->s12, s19|->s13, s19|->s14, s19|->s16, s19|->s18, s20|->s2, s20|->s3, s20|->s4, s20|->s7, s20|->s9, s20|->s10, s20|->s11, s20|->s12, s20|->s13, s20|->s18, s20|->s19, s21|->s2, s21|->s3, s21|->s6, s21|->s8, s21|->s15, s21|->s19, s21|->s20, s22|->s3, s22|->s6, s22|->s7, s22|->s8, s22|->s10, s22|->s11, s22|->s12, s22|->s16, s22|->s18, s22|->s19, s23|->s2, s23|->s7, s23|->s9, s23|->s10, s23|->s11, s23|->s12, s23|->s15, s23|->s18, s23|->s19, s23|->s20, s24|->s0, s24|->s1, s24|->s2, s24|->s3, s24|->s5, s24|->s6, s24|->s8, s24|->s10, s24|->s12, s24|->s15, s24|->s17, s24|->s19, s24|->s20, s24|->s22, s24|->s23, s25|->s0, s25|->s2, s25|->s4, s25|->s6, s25|->s8, s25|->s9, s25|->s10, s25|->s12, s25|->s13, s25|->s14, s25|->s15, s25|->s16, s25|->s17, s25|->s18, s25|->s20, s26|->s1, s26|->s2, s26|->s3, s26|->s4, s26|->s8, s26|->s9, s26|->s13, s26|->s15, s26|->s17, s26|->s23, s26|->s24, s26|->s25, s27|->s0, s27|->s3, s27|->s6, s27|->s7, s27|->s8, s27|->s9, s27|->s11, s27|->s12, s27|->s13, s27|->s16, s27|->s17, s27|->s19, s27|->s23, s27|->s25, s27|->s26, s28|->s0, s28|->s5, s28|->s6, s28|->s7, s28|->s8, s28|->s9, s28|->s10, s28|->s11, s28|->s13, s28|->s14, s28|->s15, s28|->s16, s28|->s17, s28|->s20, s28|->s22, s28|->s25, s28|->s26, s29|->s0, s29|->s3, s29|->s4, s29|->s6, s29|->s7, s29|->s8, s29|->s10, s29|->s12, s29|->s13, s29|->s14, s29|->s15, s29|->s17, s29|->s18, s29|->s19, s29|->s20, s29|->s21, s29|->s25} &
    e_res={r1|->r0, r3|->r0, r3|->r1, r3|->r2, r4|->r0, r4|->r1, r4|->r2, r4|->r3, r5|->r1, r5|->r2, r6|->r2, r6|->r3, r7|->r1, r7|->r5, r8|->r0, r8|->r1, r8|->r2, r8|->r6, r8|->r7, r9|->r1, r9|->r3, r9|->r4, r9|->r7, r10|->r2, r10|->r4, r10|->r6, r10|->r7, r10|->r9, r11|->r0, r11|->r3, r11|->r5, r11|->r6, r11|->r9, r12|->r0, r12|->r2, r12|->r4, r12|->r7, r12|->r8, r12|->r11, r13|->r1, r13|->r3, r13|->r5, r13|->r6, r13|->r7, r13|->r10, r14|->r2, r14|->r3, r14|->r5, r14|->r8, r14|->r11, r14|->r12, r15|->r2, r15|->r3, r15|->r11, r15|->r13, r16|->r0, r16|->r1, r16|->r2, r16|->r3, r16|->r5, r16|->r7, r16|->r8, r16|->r9, r16|->r11, r17|->r2, r17|->r6, r17|->r7, r17|->r8, r17|->r11, r17|->r12, r17|->r13, r17|->r14, r17|->r15, r18|->r0, r18|->r2, r18|->r6, r18|->r7, r18|->r9, r18|->r10, r18|->r12, r18|->r15, r18|->r16, r19|->r4, r19|->r5, r19|->r7, r19|->r8, r19|->r9, r19|->r12, r19|->r17, r20|->r0, r20|->r2, r20|->r3, r20|->r4, r20|->r6, r20|->r7, r20|->r9, r20|->r11, r20|->r14, r20|->r16, r20|->r17, r20|->r18, r21|->r0, r21|->r1, r21|->r2, r21|->r3, r21|->r5, r21|->r6, r21|->r12, r21|->r14, r21|->r17, r21|->r18, r22|->r1, r22|->r6, r22|->r7, r22|->r9, r22|->r10, r22|->r12, r22|->r14, r22|->r15, r22|->r17, r22|->r18, r22|->r20, r22|->r21, r23|->r0, r23|->r1, r23|->r8, r23|->r9, r23|->r10, r23|->r11, r23|->r13, r23|->r15, r23|->r16, r24|->r6, r24|->r7, r24|->r8, r24|->r9, r24|->r12, r24|->r14, r24|->r15, r24|->r16, r24|->r20, r25|->r0, r25|->r1, r25|->r2, r25|->r4, r25|->r5, r25|->r6, r25|->r9, r25|->r11, r25|->r13, r25|->r14, r25|->r15, r25|->r17, r25|->r19, r25|->r21, r25|->r23, r25|->r24, r26|->r0, r26|->r4, r26|->r5, r26|->r7, r26|->r8, r26|->r12, r26|->r14, r26|->r17, r26|->r18, r26|->r21, r26|->r22, r26|->r23, r27|->r0, r27|->r2, r27|->r5, r27|->r6, r27|->r7, r27|->r8, r27|->r10, r27|->r11, r27|->r12, r27|->r15, r27|->r16, r27|->r20, r27|->r21, r27|->r22, r27|->r23, r28|->r1, r28|->r4, r28|->r5, r28|->r6, r28|->r8, r28|->r9, r28|->r11, r28|->r12, r28|->r13, r28|->r16, r28|->r18, r28|->r19, r28|->r21, r28|->r22, r28|->r24, r28|->r27, r29|->r0, r29|->r1, r29|->r7, r29|->r9, r29|->r11, r29|->r12, r29|->r14, r29|->r15, r29|->r16, r29|->r17, r29|->r18, r29|->r20, r29|->r22, r29|->r23, r29|->r27, r29|->r28} &
    rules={rule0|->(rec(su:s21,re:r27,mo:per,pr: 0,co:{c9,c0,c1,c8})), rule1|->(rec(su:s10,re:r3,mo:per,pr: 4,co:{c5})), rule2|->(rec(su:s13,re:r22,mo:pro,pr: 0,co:{c9,c3,c8,c1,c0,c5})), rule3|->(rec(su:s23,re:r26,mo:pro,pr: 1,co:{c9,c7,c6})), rule4|->(rec(su:s23,re:r6,mo:pro,pr: 2,co:{c3,c5,c9,c8})), rule5|->(rec(su:s15,re:r1,mo:per,pr: 2,co:{c6,c9,c5})), rule6|->(rec(su:s25,re:r9,mo:pro,pr: 1,co:{c3,c5,c2,c7})), rule7|->(rec(su:s22,re:r11,mo:pro,pr: 1,co:{c9,c7,c8,c5})), rule8|->(rec(su:s25,re:r16,mo:pro,pr: 1,co:{c5,c4,c3,c0,c2,c1,c9})), rule9|->(rec(su:s9,re:r6,mo:pro,pr: 2,co:{c4})), rule10|->(rec(su:s5,re:r0,mo:per,pr: 1,co:{c9,c0,c5,c3,c6})), rule11|->(rec(su:s14,re:r14,mo:per,pr: 4,co:{c7}))}

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