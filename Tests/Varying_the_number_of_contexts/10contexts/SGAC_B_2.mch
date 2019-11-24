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
    V_SUB={s9, s8, s3, s2, s1, s0, s7, s6, s5, s4, s19, s18, s13, s12, s11, s10, s17, s16, s15, s14, s22, s23, s20, s21, s26, s27, s24, s25, s28, s29};
    /*resource vertex type*/
    V_RES={r29, r28, r27, r26, r25, r24, r23, r22, r21, r20, r16, r17, r14, r15, r12, r13, r10, r11, r18, r19, r4, r5, r6, r7, r0, r1, r2, r3, r8, r9};
    /*rule type*/
    RULE_T={rule9, rule8, rule3, rule2, rule1, rule0, rule7, rule6, rule5, rule4, rule11, rule10};
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
    e_sub={s9|->s1, s9|->s2, s9|->s3, s9|->s4, s9|->s8, s8|->s0, s8|->s5, s8|->s6, s3|->s0, s3|->s2, s2|->s1, s1|->s0, s7|->s1, s7|->s2, s7|->s4, s5|->s0, s5|->s1, s5|->s4, s4|->s2, s4|->s3, s19|->s3, s19|->s5, s19|->s6, s19|->s7, s19|->s8, s19|->s11, s19|->s12, s19|->s15, s19|->s16, s19|->s17, s19|->s18, s18|->s0, s18|->s3, s18|->s5, s18|->s6, s18|->s7, s18|->s9, s18|->s10, s13|->s1, s13|->s4, s13|->s6, s13|->s9, s13|->s10, s13|->s12, s12|->s3, s12|->s5, s12|->s8, s12|->s9, s11|->s5, s11|->s6, s11|->s9, s10|->s1, s10|->s2, s10|->s3, s10|->s7, s10|->s8, s10|->s9, s17|->s0, s17|->s1, s17|->s2, s17|->s6, s17|->s7, s17|->s9, s17|->s10, s17|->s11, s17|->s13, s17|->s14, s17|->s16, s16|->s0, s16|->s1, s16|->s3, s16|->s5, s16|->s7, s16|->s9, s16|->s12, s16|->s13, s16|->s14, s16|->s15, s15|->s0, s15|->s1, s15|->s2, s15|->s5, s15|->s7, s15|->s8, s14|->s2, s14|->s3, s14|->s4, s14|->s5, s14|->s6, s14|->s8, s14|->s10, s14|->s13, s22|->s0, s22|->s1, s22|->s3, s22|->s4, s22|->s5, s22|->s7, s22|->s16, s22|->s17, s22|->s18, s22|->s19, s22|->s20, s23|->s0, s23|->s1, s23|->s3, s23|->s6, s23|->s8, s23|->s10, s23|->s11, s23|->s12, s23|->s13, s23|->s14, s23|->s15, s23|->s17, s23|->s18, s20|->s1, s20|->s2, s20|->s3, s20|->s4, s20|->s7, s20|->s9, s20|->s10, s20|->s12, s20|->s17, s20|->s18, s20|->s19, s21|->s0, s21|->s1, s21|->s2, s21|->s9, s21|->s11, s21|->s13, s21|->s18, s26|->s2, s26|->s3, s26|->s7, s26|->s8, s26|->s10, s26|->s11, s26|->s12, s26|->s13, s26|->s17, s26|->s19, s26|->s21, s26|->s24, s27|->s1, s27|->s4, s27|->s5, s27|->s6, s27|->s7, s27|->s8, s27|->s10, s27|->s11, s27|->s12, s27|->s13, s27|->s14, s27|->s15, s27|->s19, s27|->s20, s27|->s26, s24|->s5, s24|->s6, s24|->s9, s24|->s15, s25|->s0, s25|->s3, s25|->s5, s25|->s8, s25|->s9, s25|->s11, s25|->s12, s25|->s13, s25|->s15, s25|->s16, s25|->s17, s25|->s21, s25|->s23, s25|->s24, s28|->s0, s28|->s3, s28|->s5, s28|->s6, s28|->s9, s28|->s13, s28|->s18, s28|->s19, s28|->s22, s28|->s24, s28|->s25, s28|->s26, s28|->s27, s29|->s2, s29|->s6, s29|->s8, s29|->s9, s29|->s10, s29|->s11, s29|->s14, s29|->s17, s29|->s18, s29|->s22, s29|->s28} &
    e_res={r29|->r3, r29|->r6, r29|->r10, r29|->r11, r29|->r12, r29|->r13, r29|->r14, r29|->r15, r29|->r18, r29|->r19, r29|->r21, r29|->r22, r29|->r23, r29|->r24, r29|->r25, r29|->r27, r29|->r28, r28|->r0, r28|->r1, r28|->r2, r28|->r7, r28|->r8, r28|->r11, r28|->r12, r28|->r13, r28|->r14, r28|->r15, r28|->r18, r28|->r19, r28|->r21, r28|->r22, r28|->r23, r28|->r25, r27|->r2, r27|->r4, r27|->r5, r27|->r6, r27|->r7, r27|->r9, r27|->r18, r27|->r20, r27|->r21, r27|->r25, r27|->r26, r26|->r0, r26|->r5, r26|->r8, r26|->r10, r26|->r13, r26|->r15, r26|->r16, r26|->r20, r26|->r21, r26|->r24, r26|->r25, r25|->r1, r25|->r2, r25|->r4, r25|->r6, r25|->r7, r25|->r8, r25|->r9, r25|->r11, r25|->r13, r25|->r17, r25|->r18, r25|->r19, r25|->r20, r25|->r21, r25|->r23, r25|->r24, r24|->r0, r24|->r1, r24|->r4, r24|->r6, r24|->r9, r24|->r10, r24|->r11, r24|->r13, r24|->r15, r24|->r16, r24|->r17, r24|->r18, r24|->r20, r24|->r21, r23|->r1, r23|->r2, r23|->r3, r23|->r4, r23|->r5, r23|->r11, r23|->r13, r23|->r14, r23|->r16, r23|->r20, r23|->r22, r22|->r0, r22|->r2, r22|->r6, r22|->r8, r22|->r10, r22|->r12, r22|->r17, r22|->r19, r22|->r20, r22|->r21, r21|->r0, r21|->r4, r21|->r5, r21|->r7, r21|->r8, r21|->r9, r21|->r13, r21|->r14, r21|->r15, r21|->r17, r21|->r18, r20|->r1, r20|->r2, r20|->r4, r20|->r5, r20|->r6, r20|->r7, r20|->r10, r20|->r11, r20|->r15, r20|->r19, r16|->r0, r16|->r1, r16|->r2, r16|->r3, r16|->r5, r16|->r9, r16|->r10, r16|->r11, r16|->r12, r16|->r14, r17|->r4, r17|->r5, r17|->r6, r17|->r9, r17|->r12, r17|->r13, r17|->r16, r14|->r0, r14|->r1, r14|->r4, r14|->r7, r14|->r9, r14|->r12, r14|->r13, r15|->r2, r15|->r3, r15|->r4, r15|->r5, r15|->r6, r15|->r9, r15|->r12, r15|->r13, r12|->r3, r12|->r4, r12|->r6, r12|->r7, r13|->r0, r13|->r3, r10|->r1, r10|->r2, r10|->r4, r10|->r6, r10|->r7, r10|->r9, r11|->r2, r11|->r4, r11|->r6, r11|->r8, r11|->r10, r18|->r0, r18|->r2, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r8, r18|->r10, r18|->r11, r18|->r16, r18|->r17, r19|->r0, r19|->r3, r19|->r5, r19|->r6, r19|->r8, r19|->r9, r19|->r10, r19|->r13, r19|->r15, r19|->r17, r4|->r1, r4|->r3, r5|->r1, r5|->r3, r5|->r4, r6|->r1, r6|->r2, r6|->r4, r7|->r0, r7|->r1, r7|->r2, r7|->r3, r3|->r0, r3|->r1, r8|->r3, r8|->r4, r9|->r3, r9|->r7} &
    rules={rule9|->(rec(su:s5,re:r18,mo:per,pr: 3,co:{c1,c3,c4})), rule8|->(rec(su:s5,re:r2,mo:pro,pr: 4,co:{c4,c5,c8})), rule3|->(rec(su:s27,re:r15,mo:per,pr: 1,co:{c2,c6,c8})), rule2|->(rec(su:s2,re:r26,mo:pro,pr: 0,co:{c1,c4,c0,c6,c8})), rule1|->(rec(su:s27,re:r24,mo:pro,pr: 2,co:{c1,c4,c7,c8})), rule0|->(rec(su:s13,re:r21,mo:pro,pr: 2,co:{c0,c5,c7,c8,c4})), rule7|->(rec(su:s3,re:r17,mo:pro,pr: 3,co:{c0,c8,c2})), rule6|->(rec(su:s16,re:r28,mo:pro,pr: 2,co:{c8,c6,c1,c0,c7,c2})), rule5|->(rec(su:s17,re:r3,mo:per,pr: 0,co:{c9,c1,c3,c8,c4})), rule4|->(rec(su:s23,re:r6,mo:pro,pr: 3,co:{c1,c5,c7,c0,c8,c6,c2})), rule11|->(rec(su:s12,re:r3,mo:pro,pr: 2,co:{c1,c7,c9,c0,c4,c5,c6})), rule10|->(rec(su:s10,re:r13,mo:pro,pr: 4,co:{c1,c4}))}

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