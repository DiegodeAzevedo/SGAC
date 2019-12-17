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
    e_sub={s1|->s0, s2|->s1, s4|->s1, s4|->s2, s4|->s3, s5|->s0, s5|->s2, s6|->s2, s7|->s2, s7|->s3, s7|->s4, s7|->s5, s7|->s6, s8|->s3, s8|->s6, s8|->s7, s9|->s0, s9|->s2, s9|->s3, s9|->s7, s10|->s4, s10|->s5, s10|->s7, s10|->s9, s11|->s3, s11|->s4, s11|->s6, s11|->s7, s12|->s0, s12|->s6, s12|->s8, s12|->s9, s12|->s11, s13|->s5, s13|->s8, s13|->s9, s13|->s11, s14|->s0, s14|->s2, s14|->s3, s14|->s5, s14|->s6, s14|->s7, s14|->s9, s14|->s11, s14|->s12, s14|->s13, s15|->s0, s15|->s2, s15|->s6, s15|->s7, s15|->s8, s15|->s9, s15|->s14, s16|->s0, s16|->s8, s16|->s9, s16|->s10, s16|->s11, s16|->s12, s16|->s15, s17|->s0, s17|->s3, s17|->s4, s17|->s11, s17|->s12, s17|->s15, s17|->s16, s18|->s0, s18|->s2, s18|->s3, s18|->s4, s18|->s6, s18|->s11, s18|->s12, s18|->s13, s18|->s14, s18|->s16, s18|->s17, s19|->s1, s19|->s2, s19|->s3, s19|->s5, s19|->s6, s19|->s9, s19|->s10, s19|->s11, s19|->s12, s19|->s13, s19|->s14, s19|->s15, s19|->s16, s19|->s17, s20|->s2, s20|->s3, s20|->s4, s20|->s7, s20|->s10, s20|->s13, s20|->s19, s21|->s0, s21|->s2, s21|->s4, s21|->s5, s21|->s7, s21|->s8, s21|->s9, s21|->s10, s21|->s13, s21|->s14, s21|->s15, s21|->s18, s21|->s19, s21|->s20, s22|->s1, s22|->s6, s22|->s8, s22|->s9, s22|->s10, s22|->s12, s22|->s13, s22|->s14, s22|->s17, s22|->s19, s22|->s21, s23|->s0, s23|->s2, s23|->s6, s23|->s7, s23|->s9, s23|->s11, s23|->s13, s23|->s15, s23|->s16, s23|->s18, s23|->s22, s24|->s4, s24|->s5, s24|->s7, s24|->s8, s24|->s10, s24|->s14, s24|->s16, s24|->s18, s24|->s20, s24|->s21, s25|->s0, s25|->s1, s25|->s3, s25|->s5, s25|->s6, s25|->s7, s25|->s17, s25|->s20, s25|->s22, s26|->s0, s26|->s1, s26|->s2, s26|->s3, s26|->s6, s26|->s7, s26|->s10, s26|->s12, s26|->s13, s26|->s15, s26|->s16, s26|->s18, s26|->s20, s26|->s21, s26|->s22, s26|->s25, s27|->s1, s27|->s2, s27|->s3, s27|->s4, s27|->s5, s27|->s6, s27|->s7, s27|->s9, s27|->s14, s27|->s15, s27|->s16, s27|->s18, s27|->s25, s28|->s2, s28|->s5, s28|->s6, s28|->s11, s28|->s12, s28|->s13, s28|->s15, s28|->s19, s28|->s21, s28|->s22, s28|->s23, s28|->s25, s28|->s26, s28|->s27, s29|->s0, s29|->s2, s29|->s3, s29|->s4, s29|->s6, s29|->s7, s29|->s9, s29|->s10, s29|->s12, s29|->s13, s29|->s16, s29|->s19, s29|->s21, s29|->s22, s29|->s23, s29|->s24, s29|->s25, s29|->s26, s29|->s27, s29|->s28} &
    e_res={r2|->r0, r2|->r1, r3|->r2, r4|->r1, r4|->r2, r5|->r1, r5|->r2, r5|->r3, r6|->r0, r6|->r3, r7|->r0, r7|->r2, r7|->r3, r7|->r4, r7|->r5, r7|->r6, r8|->r1, r8|->r3, r8|->r5, r9|->r2, r9|->r4, r9|->r5, r9|->r6, r9|->r8, r10|->r0, r10|->r1, r10|->r2, r10|->r7, r10|->r8, r11|->r1, r11|->r2, r11|->r7, r11|->r10, r12|->r0, r12|->r1, r12|->r5, r12|->r9, r12|->r10, r12|->r11, r13|->r4, r13|->r8, r13|->r12, r14|->r1, r14|->r4, r14|->r5, r14|->r7, r14|->r8, r14|->r9, r14|->r11, r14|->r12, r15|->r0, r15|->r1, r15|->r4, r15|->r7, r15|->r13, r15|->r14, r16|->r1, r16|->r2, r16|->r3, r16|->r4, r16|->r5, r16|->r6, r16|->r8, r16|->r11, r16|->r12, r16|->r13, r16|->r14, r17|->r0, r17|->r1, r17|->r2, r17|->r4, r17|->r5, r17|->r8, r17|->r11, r17|->r13, r17|->r14, r17|->r15, r18|->r2, r18|->r6, r18|->r8, r18|->r9, r18|->r10, r18|->r12, r18|->r13, r18|->r14, r18|->r15, r19|->r0, r19|->r1, r19|->r2, r19|->r3, r19|->r10, r19|->r11, r19|->r12, r19|->r18, r20|->r2, r20|->r4, r20|->r5, r20|->r6, r20|->r7, r20|->r8, r20|->r11, r20|->r14, r20|->r16, r20|->r17, r20|->r19, r21|->r1, r21|->r2, r21|->r3, r21|->r5, r21|->r7, r21|->r8, r21|->r9, r21|->r10, r21|->r13, r21|->r17, r21|->r18, r21|->r19, r22|->r0, r22|->r3, r22|->r4, r22|->r6, r22|->r9, r22|->r14, r22|->r15, r22|->r16, r22|->r21, r23|->r3, r23|->r5, r23|->r7, r23|->r10, r23|->r13, r23|->r15, r23|->r16, r23|->r17, r23|->r18, r23|->r21, r24|->r0, r24|->r3, r24|->r4, r24|->r5, r24|->r6, r24|->r7, r24|->r9, r24|->r10, r24|->r11, r24|->r13, r24|->r16, r24|->r17, r24|->r18, r24|->r19, r24|->r23, r25|->r6, r25|->r7, r25|->r8, r25|->r9, r25|->r13, r25|->r14, r25|->r15, r25|->r16, r25|->r17, r25|->r18, r25|->r19, r25|->r20, r25|->r21, r25|->r23, r26|->r0, r26|->r1, r26|->r2, r26|->r3, r26|->r4, r26|->r5, r26|->r7, r26|->r8, r26|->r9, r26|->r10, r26|->r11, r26|->r14, r26|->r15, r26|->r17, r26|->r19, r26|->r20, r26|->r22, r26|->r23, r27|->r2, r27|->r3, r27|->r4, r27|->r5, r27|->r9, r27|->r12, r27|->r13, r27|->r14, r27|->r21, r27|->r22, r27|->r23, r27|->r24, r27|->r26, r28|->r1, r28|->r2, r28|->r4, r28|->r10, r28|->r17, r28|->r21, r28|->r24, r29|->r0, r29|->r1, r29|->r5, r29|->r9, r29|->r10, r29|->r12, r29|->r13, r29|->r16, r29|->r17, r29|->r20, r29|->r24} &
    rules={rule0|->(rec(su:s24,re:r27,mo:pro,pr: 0,co:{c2,c5,c7,c1,c9})), rule1|->(rec(su:s5,re:r7,mo:per,pr: 2,co:{c3,c6,c7,c5,c9,c0,c4})), rule2|->(rec(su:s3,re:r5,mo:pro,pr: 1,co:{c6,c9,c4,c1,c8,c2,c0})), rule3|->(rec(su:s11,re:r15,mo:per,pr: 1,co:{c1,c6,c2,c7,c4})), rule4|->(rec(su:s11,re:r12,mo:per,pr: 0,co:{c1})), rule5|->(rec(su:s13,re:r22,mo:pro,pr: 0,co:{c8,c4,c2,c9})), rule6|->(rec(su:s15,re:r24,mo:per,pr: 3,co:{c7,c2,c6,c1})), rule7|->(rec(su:s9,re:r3,mo:per,pr: 2,co:{c6,c7,c2,c5,c0})), rule8|->(rec(su:s15,re:r26,mo:pro,pr: 1,co:{c8,c5,c1,c2,c9,c3,c0})), rule9|->(rec(su:s28,re:r6,mo:per,pr: 0,co:{c3,c4,c0,c8})), rule10|->(rec(su:s23,re:r13,mo:per,pr: 1,co:{c4})), rule11|->(rec(su:s18,re:r0,mo:pro,pr: 1,co:{c3,c1,c4,c8}))}

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