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
    e_sub={s2|->s0, s3|->s2, s4|->s3, s5|->s0, s5|->s3, s5|->s4, s6|->s0, s6|->s1, s7|->s0, s7|->s1, s7|->s4, s7|->s6, s8|->s1, s8|->s2, s8|->s3, s8|->s6, s9|->s0, s9|->s1, s9|->s2, s9|->s3, s9|->s4, s9|->s5, s9|->s7, s9|->s8, s10|->s0, s10|->s2, s10|->s6, s10|->s7, s10|->s9, s11|->s0, s11|->s3, s11|->s5, s11|->s10, s12|->s0, s12|->s2, s12|->s3, s12|->s4, s12|->s7, s12|->s8, s12|->s10, s12|->s11, s13|->s1, s13|->s5, s13|->s7, s13|->s8, s13|->s9, s13|->s10, s13|->s11, s14|->s0, s14|->s1, s14|->s2, s14|->s3, s14|->s4, s14|->s5, s14|->s8, s14|->s11, s14|->s12, s14|->s13, s15|->s0, s15|->s1, s15|->s2, s15|->s3, s15|->s4, s15|->s5, s15|->s8, s15|->s12, s15|->s13, s16|->s1, s16|->s2, s16|->s4, s16|->s5, s16|->s9, s16|->s10, s16|->s12, s16|->s13, s16|->s15, s17|->s1, s17|->s6, s17|->s7, s17|->s8, s17|->s13, s18|->s2, s18|->s5, s18|->s8, s18|->s11, s18|->s15, s18|->s16, s18|->s17, s19|->s1, s19|->s2, s19|->s4, s19|->s6, s19|->s7, s19|->s12, s19|->s15, s19|->s18, s20|->s0, s20|->s1, s20|->s2, s20|->s5, s20|->s9, s20|->s10, s20|->s11, s20|->s14, s20|->s16, s20|->s17, s20|->s18, s21|->s1, s21|->s5, s21|->s6, s21|->s7, s21|->s9, s21|->s11, s21|->s14, s21|->s16, s21|->s17, s21|->s18, s21|->s20, s22|->s1, s22|->s3, s22|->s4, s22|->s6, s22|->s8, s22|->s10, s22|->s11, s22|->s13, s22|->s15, s22|->s16, s22|->s18, s22|->s19, s22|->s20, s23|->s0, s23|->s1, s23|->s3, s23|->s6, s23|->s10, s23|->s12, s23|->s14, s23|->s16, s23|->s17, s23|->s20, s23|->s21, s24|->s0, s24|->s1, s24|->s2, s24|->s5, s24|->s6, s24|->s7, s24|->s9, s24|->s11, s24|->s14, s24|->s15, s24|->s17, s24|->s19, s24|->s20, s24|->s21, s24|->s23, s25|->s2, s25|->s4, s25|->s5, s25|->s9, s25|->s12, s25|->s13, s25|->s14, s25|->s18, s25|->s19, s25|->s20, s25|->s21, s25|->s24, s26|->s0, s26|->s2, s26|->s3, s26|->s5, s26|->s7, s26|->s8, s26|->s9, s26|->s12, s26|->s14, s26|->s16, s26|->s17, s26|->s18, s27|->s0, s27|->s1, s27|->s2, s27|->s3, s27|->s4, s27|->s5, s27|->s6, s27|->s8, s27|->s10, s27|->s12, s27|->s14, s27|->s17, s27|->s26, s28|->s0, s28|->s1, s28|->s2, s28|->s3, s28|->s5, s28|->s6, s28|->s8, s28|->s9, s28|->s11, s28|->s15, s28|->s16, s28|->s17, s28|->s20, s28|->s21, s28|->s22, s28|->s26, s29|->s0, s29|->s2, s29|->s3, s29|->s5, s29|->s6, s29|->s7, s29|->s8, s29|->s10, s29|->s11, s29|->s12, s29|->s15, s29|->s17, s29|->s18, s29|->s19, s29|->s21, s29|->s23, s29|->s24, s29|->s25, s29|->s27, s29|->s28} &
    e_res={r3|->r0, r3|->r1, r3|->r2, r4|->r3, r5|->r1, r5|->r4, r6|->r4, r7|->r1, r7|->r2, r7|->r3, r7|->r4, r7|->r6, r8|->r1, r8|->r2, r8|->r4, r8|->r5, r8|->r6, r8|->r7, r9|->r0, r9|->r1, r9|->r5, r10|->r3, r10|->r5, r10|->r9, r11|->r1, r11|->r3, r11|->r4, r11|->r9, r12|->r0, r12|->r1, r12|->r4, r12|->r5, r12|->r6, r12|->r7, r12|->r9, r12|->r11, r13|->r0, r13|->r1, r13|->r2, r13|->r6, r13|->r7, r13|->r10, r14|->r0, r14|->r2, r14|->r4, r14|->r7, r14|->r8, r14|->r10, r14|->r11, r15|->r4, r15|->r5, r15|->r8, r15|->r9, r15|->r11, r15|->r13, r15|->r14, r16|->r2, r16|->r4, r16|->r6, r16|->r10, r16|->r11, r16|->r12, r16|->r14, r17|->r1, r17|->r2, r17|->r4, r17|->r6, r17|->r7, r17|->r10, r17|->r13, r18|->r2, r18|->r3, r18|->r4, r18|->r5, r18|->r7, r18|->r9, r18|->r12, r18|->r15, r18|->r17, r19|->r0, r19|->r5, r19|->r6, r19|->r8, r19|->r14, r19|->r18, r20|->r0, r20|->r5, r20|->r6, r20|->r7, r20|->r10, r20|->r11, r20|->r12, r20|->r14, r20|->r16, r20|->r18, r20|->r19, r21|->r0, r21|->r4, r21|->r7, r21|->r12, r21|->r13, r21|->r14, r21|->r16, r21|->r17, r21|->r18, r22|->r0, r22|->r1, r22|->r3, r22|->r4, r22|->r5, r22|->r8, r22|->r9, r22|->r11, r22|->r13, r22|->r15, r22|->r16, r22|->r20, r22|->r21, r23|->r3, r23|->r4, r23|->r5, r23|->r6, r23|->r13, r23|->r14, r23|->r18, r23|->r19, r23|->r20, r23|->r21, r23|->r22, r24|->r2, r24|->r4, r24|->r6, r24|->r7, r24|->r13, r24|->r17, r24|->r18, r24|->r20, r24|->r23, r25|->r0, r25|->r2, r25|->r3, r25|->r5, r25|->r6, r25|->r7, r25|->r8, r25|->r9, r25|->r10, r25|->r11, r25|->r14, r25|->r15, r25|->r16, r25|->r17, r25|->r19, r25|->r20, r25|->r21, r25|->r23, r26|->r3, r26|->r4, r26|->r8, r26|->r9, r26|->r14, r26|->r18, r26|->r21, r26|->r22, r26|->r23, r26|->r25, r27|->r0, r27|->r2, r27|->r5, r27|->r6, r27|->r7, r27|->r8, r27|->r10, r27|->r12, r27|->r13, r27|->r16, r27|->r17, r27|->r18, r27|->r19, r27|->r22, r27|->r23, r27|->r26, r28|->r0, r28|->r4, r28|->r5, r28|->r6, r28|->r13, r28|->r14, r28|->r20, r28|->r21, r28|->r24, r28|->r25, r29|->r0, r29|->r1, r29|->r3, r29|->r4, r29|->r5, r29|->r6, r29|->r9, r29|->r12, r29|->r13, r29|->r14, r29|->r15, r29|->r24, r29|->r25, r29|->r28} &
    rules={rule0|->(rec(su:s1,re:r26,mo:pro,pr: 0,co:{c8,c5,c2,c4})), rule1|->(rec(su:s1,re:r7,mo:pro,pr: 2,co:{c8,c6,c2})), rule2|->(rec(su:s19,re:r5,mo:pro,pr: 0,co:{c8,c2,c3,c5,c1,c9})), rule3|->(rec(su:s15,re:r14,mo:per,pr: 4,co:{c1,c4,c6,c0,c5,c7})), rule4|->(rec(su:s24,re:r18,mo:pro,pr: 3,co:{c8,c9,c1,c4,c3})), rule5|->(rec(su:s22,re:r12,mo:per,pr: 1,co:{c9})), rule6|->(rec(su:s25,re:r17,mo:per,pr: 3,co:{c5,c8,c2,c3,c7})), rule7|->(rec(su:s2,re:r20,mo:pro,pr: 0,co:{c0,c1,c5,c4,c2,c8,c7})), rule8|->(rec(su:s27,re:r11,mo:per,pr: 0,co:{c6,c8,c7,c9,c3,c5,c1})), rule9|->(rec(su:s2,re:r2,mo:per,pr: 3,co:{c0})), rule10|->(rec(su:s8,re:r7,mo:per,pr: 4,co:{c7,c9,c6})), rule11|->(rec(su:s25,re:r3,mo:pro,pr: 0,co:{c6}))}

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