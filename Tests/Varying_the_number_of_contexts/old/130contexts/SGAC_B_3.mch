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
    e_sub={s2|->s0, s2|->s1, s3|->s0, s4|->s2, s4|->s3, s5|->s0, s5|->s1, s5|->s2, s5|->s3, s6|->s2, s6|->s3, s6|->s4, s6|->s5, s7|->s1, s7|->s4, s8|->s3, s8|->s4, s8|->s5, s8|->s6, s9|->s0, s9|->s3, s9|->s4, s9|->s5, s9|->s7, s9|->s8, s10|->s0, s10|->s5, s10|->s7, s11|->s0, s11|->s1, s11|->s2, s11|->s3, s11|->s5, s11|->s6, s11|->s7, s11|->s9, s11|->s10, s12|->s1, s12|->s2, s12|->s7, s12|->s8, s12|->s9, s13|->s0, s13|->s2, s13|->s5, s13|->s8, s13|->s11, s14|->s0, s14|->s3, s14|->s5, s14|->s7, s14|->s8, s14|->s9, s14|->s11, s15|->s1, s15|->s2, s15|->s5, s15|->s6, s15|->s7, s15|->s10, s15|->s12, s16|->s0, s16|->s2, s16|->s4, s16|->s7, s16|->s8, s16|->s10, s16|->s12, s16|->s13, s17|->s0, s17|->s1, s17|->s2, s17|->s5, s17|->s7, s17|->s8, s17|->s12, s17|->s13, s18|->s2, s18|->s4, s18|->s7, s18|->s8, s18|->s9, s18|->s16, s19|->s0, s19|->s1, s19|->s4, s19|->s8, s19|->s9, s19|->s11, s19|->s14, s19|->s17, s20|->s2, s20|->s4, s20|->s8, s20|->s9, s20|->s10, s20|->s12, s20|->s13, s20|->s14, s20|->s15, s20|->s16, s20|->s17, s21|->s0, s21|->s1, s21|->s5, s21|->s7, s21|->s9, s21|->s10, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s17, s21|->s20, s22|->s0, s22|->s1, s22|->s2, s22|->s5, s22|->s8, s22|->s10, s22|->s12, s22|->s13, s22|->s14, s22|->s15, s22|->s18, s22|->s19, s22|->s20, s23|->s4, s23|->s6, s23|->s9, s23|->s11, s23|->s12, s23|->s13, s23|->s15, s23|->s16, s23|->s19, s23|->s22, s24|->s1, s24|->s4, s24|->s6, s24|->s7, s24|->s9, s24|->s14, s24|->s16, s24|->s18, s24|->s19, s25|->s3, s25|->s5, s25|->s6, s25|->s8, s25|->s9, s25|->s10, s25|->s11, s25|->s12, s25|->s14, s25|->s15, s25|->s16, s25|->s19, s25|->s21, s25|->s22, s25|->s23, s25|->s24, s26|->s1, s26|->s3, s26|->s4, s26|->s5, s26|->s7, s26|->s8, s26|->s10, s26|->s12, s26|->s13, s26|->s16, s26|->s19, s26|->s23, s26|->s24, s27|->s0, s27|->s1, s27|->s2, s27|->s3, s27|->s4, s27|->s7, s27|->s8, s27|->s10, s27|->s12, s27|->s15, s27|->s17, s27|->s18, s27|->s20, s27|->s21, s27|->s22, s27|->s24, s27|->s26, s28|->s0, s28|->s1, s28|->s3, s28|->s5, s28|->s6, s28|->s7, s28|->s9, s28|->s10, s28|->s11, s28|->s19, s28|->s22, s28|->s23, s28|->s26, s29|->s0, s29|->s1, s29|->s2, s29|->s3, s29|->s4, s29|->s7, s29|->s8, s29|->s14, s29|->s18, s29|->s21, s29|->s22, s29|->s23, s29|->s24, s29|->s26, s29|->s28} &
    e_res={r2|->r0, r2|->r1, r3|->r0, r4|->r0, r4|->r3, r5|->r0, r5|->r1, r5|->r2, r5|->r4, r6|->r0, r6|->r2, r6|->r4, r6|->r5, r7|->r0, r7|->r2, r7|->r3, r7|->r4, r7|->r6, r8|->r0, r8|->r2, r8|->r3, r8|->r4, r8|->r6, r9|->r0, r9|->r1, r9|->r3, r9|->r4, r9|->r7, r9|->r8, r10|->r3, r10|->r4, r10|->r7, r11|->r1, r11|->r5, r11|->r6, r11|->r8, r11|->r10, r12|->r0, r12|->r1, r12|->r3, r12|->r5, r12|->r7, r12|->r10, r13|->r1, r13|->r4, r13|->r7, r13|->r8, r13|->r9, r13|->r10, r13|->r12, r14|->r2, r14|->r3, r14|->r5, r14|->r8, r14|->r9, r14|->r12, r15|->r1, r15|->r2, r15|->r3, r15|->r9, r15|->r10, r15|->r12, r15|->r13, r15|->r14, r16|->r0, r16|->r1, r16|->r3, r16|->r4, r16|->r8, r16|->r10, r16|->r11, r16|->r12, r16|->r14, r16|->r15, r17|->r1, r17|->r2, r18|->r3, r18|->r5, r18|->r6, r18|->r9, r18|->r10, r18|->r14, r18|->r17, r19|->r2, r19|->r4, r19|->r5, r19|->r6, r19|->r10, r19|->r11, r19|->r12, r19|->r13, r19|->r16, r19|->r17, r19|->r18, r20|->r10, r20|->r12, r20|->r16, r20|->r18, r21|->r1, r21|->r2, r21|->r3, r21|->r5, r21|->r8, r21|->r12, r21|->r16, r21|->r18, r22|->r2, r22|->r4, r22|->r5, r22|->r7, r22|->r11, r22|->r12, r22|->r14, r22|->r16, r22|->r21, r23|->r2, r23|->r3, r23|->r4, r23|->r8, r23|->r12, r23|->r14, r23|->r15, r23|->r16, r23|->r17, r23|->r18, r23|->r19, r23|->r22, r24|->r1, r24|->r7, r24|->r9, r24|->r14, r24|->r16, r24|->r18, r24|->r20, r24|->r21, r24|->r23, r25|->r1, r25|->r2, r25|->r5, r25|->r6, r25|->r12, r25|->r13, r25|->r14, r25|->r15, r25|->r19, r25|->r20, r25|->r21, r25|->r22, r25|->r23, r25|->r24, r26|->r0, r26|->r1, r26|->r11, r26|->r12, r26|->r14, r26|->r15, r26|->r18, r26|->r19, r26|->r24, r26|->r25, r27|->r1, r27|->r4, r27|->r8, r27|->r9, r27|->r10, r27|->r11, r27|->r14, r27|->r15, r27|->r17, r27|->r20, r27|->r22, r27|->r23, r28|->r1, r28|->r2, r28|->r3, r28|->r4, r28|->r5, r28|->r6, r28|->r8, r28|->r10, r28|->r11, r28|->r14, r28|->r20, r28|->r21, r28|->r22, r28|->r24, r28|->r26, r28|->r27, r29|->r2, r29|->r3, r29|->r5, r29|->r6, r29|->r8, r29|->r9, r29|->r12, r29|->r16, r29|->r17, r29|->r19, r29|->r21, r29|->r26} &
    rules={rule0|->(rec(su:s9,re:r2,mo:per,pr: 1,co:{c8})), rule1|->(rec(su:s1,re:r21,mo:pro,pr: 3,co:{c7,c8,c2,c5})), rule2|->(rec(su:s2,re:r9,mo:pro,pr: 4,co:{c2,c5})), rule3|->(rec(su:s21,re:r15,mo:per,pr: 4,co:{c4,c8,c9})), rule4|->(rec(su:s26,re:r17,mo:pro,pr: 0,co:{c7,c2,c4,c9})), rule5|->(rec(su:s6,re:r14,mo:per,pr: 0,co:{c4,c6,c3,c5,c1,c8,c0})), rule6|->(rec(su:s18,re:r29,mo:per,pr: 2,co:{c3,c6,c8,c9,c4})), rule7|->(rec(su:s26,re:r6,mo:per,pr: 2,co:{c7,c6,c1,c3})), rule8|->(rec(su:s22,re:r25,mo:per,pr: 4,co:{c7,c5,c8,c4})), rule9|->(rec(su:s23,re:r22,mo:pro,pr: 0,co:{c8,c9,c0})), rule10|->(rec(su:s0,re:r29,mo:per,pr: 4,co:{c8,c1,c0,c3,c7,c9,c6})), rule11|->(rec(su:s13,re:r28,mo:per,pr: 1,co:{c3}))}

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