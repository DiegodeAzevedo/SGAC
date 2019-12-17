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
    e_sub={s2|->s0, s2|->s1, s3|->s0, s3|->s1, s3|->s2, s4|->s0, s4|->s1, s4|->s3, s5|->s1, s5|->s2, s5|->s3, s5|->s4, s6|->s3, s6|->s4, s7|->s1, s7|->s2, s7|->s3, s7|->s4, s7|->s6, s8|->s5, s9|->s0, s9|->s3, s9|->s6, s9|->s8, s10|->s0, s10|->s1, s10|->s3, s10|->s5, s10|->s7, s10|->s9, s11|->s1, s11|->s4, s11|->s5, s11|->s6, s11|->s7, s11|->s9, s12|->s0, s12|->s5, s12|->s9, s13|->s0, s13|->s2, s13|->s3, s13|->s5, s13|->s11, s13|->s12, s14|->s2, s14|->s3, s14|->s4, s14|->s8, s15|->s0, s15|->s2, s15|->s5, s15|->s6, s15|->s8, s15|->s10, s15|->s11, s15|->s13, s16|->s2, s16|->s6, s16|->s7, s16|->s8, s16|->s10, s16|->s13, s16|->s15, s17|->s0, s17|->s1, s17|->s2, s17|->s4, s17|->s6, s17|->s7, s17|->s10, s17|->s12, s17|->s13, s18|->s0, s18|->s1, s18|->s4, s18|->s9, s18|->s11, s18|->s12, s18|->s13, s18|->s15, s18|->s17, s19|->s0, s19|->s1, s19|->s7, s19|->s8, s19|->s9, s19|->s10, s19|->s12, s19|->s14, s19|->s15, s19|->s16, s19|->s17, s19|->s18, s20|->s0, s20|->s1, s20|->s2, s20|->s3, s20|->s4, s20|->s5, s20|->s6, s20|->s8, s20|->s9, s20|->s10, s20|->s11, s20|->s13, s20|->s14, s20|->s15, s20|->s17, s21|->s0, s21|->s2, s21|->s4, s21|->s5, s21|->s6, s21|->s7, s21|->s8, s21|->s9, s21|->s12, s21|->s13, s21|->s15, s21|->s16, s21|->s17, s21|->s19, s21|->s20, s22|->s0, s22|->s1, s22|->s2, s22|->s3, s22|->s5, s22|->s8, s22|->s9, s22|->s12, s22|->s14, s22|->s17, s22|->s21, s23|->s2, s23|->s4, s23|->s6, s23|->s7, s23|->s10, s23|->s11, s23|->s14, s23|->s16, s23|->s18, s23|->s20, s24|->s1, s24|->s4, s24|->s5, s24|->s11, s24|->s13, s24|->s14, s24|->s16, s24|->s17, s24|->s19, s24|->s20, s24|->s22, s25|->s0, s25|->s1, s25|->s2, s25|->s3, s25|->s4, s25|->s11, s25|->s14, s25|->s17, s25|->s21, s25|->s22, s25|->s24, s26|->s0, s26|->s2, s26|->s5, s26|->s8, s26|->s14, s26|->s15, s26|->s17, s27|->s1, s27|->s2, s27|->s3, s27|->s5, s27|->s6, s27|->s7, s27|->s9, s27|->s10, s27|->s11, s27|->s13, s27|->s14, s27|->s16, s27|->s18, s27|->s19, s27|->s23, s27|->s25, s28|->s0, s28|->s2, s28|->s3, s28|->s4, s28|->s7, s28|->s9, s28|->s12, s28|->s13, s28|->s18, s28|->s19, s28|->s21, s28|->s24, s28|->s25, s29|->s0, s29|->s1, s29|->s3, s29|->s5, s29|->s7, s29|->s8, s29|->s9, s29|->s12, s29|->s13, s29|->s14, s29|->s20, s29|->s22, s29|->s24, s29|->s26, s29|->s28} &
    e_res={r1|->r0, r3|->r1, r3|->r2, r4|->r3, r5|->r0, r5|->r1, r5|->r3, r6|->r4, r7|->r0, r7|->r3, r7|->r4, r8|->r0, r8|->r1, r8|->r2, r8|->r3, r8|->r7, r9|->r0, r9|->r2, r9|->r3, r9|->r5, r9|->r6, r9|->r7, r9|->r8, r10|->r1, r10|->r2, r10|->r3, r10|->r5, r10|->r7, r11|->r0, r11|->r1, r11|->r2, r11|->r3, r11|->r6, r11|->r10, r12|->r0, r12|->r2, r12|->r3, r12|->r5, r12|->r6, r12|->r8, r12|->r10, r13|->r0, r13|->r1, r13|->r4, r13|->r7, r13|->r12, r14|->r0, r14|->r2, r14|->r5, r14|->r6, r14|->r7, r14|->r9, r14|->r11, r14|->r12, r14|->r13, r15|->r2, r15|->r3, r15|->r4, r15|->r5, r15|->r8, r15|->r9, r16|->r1, r16|->r3, r16|->r4, r16|->r6, r16|->r9, r16|->r11, r16|->r12, r16|->r13, r17|->r1, r17|->r3, r17|->r4, r17|->r6, r17|->r8, r17|->r11, r17|->r12, r17|->r13, r17|->r14, r17|->r16, r18|->r0, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r7, r18|->r10, r18|->r11, r18|->r12, r18|->r13, r18|->r15, r19|->r1, r19|->r2, r19|->r3, r19|->r5, r19|->r8, r19|->r9, r19|->r11, r19|->r12, r19|->r14, r19|->r15, r20|->r1, r20|->r5, r20|->r7, r20|->r8, r20|->r11, r20|->r17, r20|->r18, r21|->r2, r21|->r4, r21|->r7, r21|->r8, r21|->r12, r21|->r16, r21|->r17, r21|->r18, r22|->r1, r22|->r3, r22|->r6, r22|->r8, r22|->r9, r22|->r10, r22|->r13, r22|->r15, r22|->r17, r22|->r19, r23|->r2, r23|->r3, r23|->r6, r23|->r7, r23|->r12, r23|->r14, r23|->r15, r23|->r16, r23|->r21, r24|->r0, r24|->r3, r24|->r6, r24|->r8, r24|->r9, r24|->r10, r24|->r11, r24|->r14, r24|->r15, r24|->r18, r24|->r20, r24|->r22, r24|->r23, r25|->r1, r25|->r2, r25|->r3, r25|->r4, r25|->r7, r25|->r8, r25|->r11, r25|->r12, r25|->r14, r25|->r16, r25|->r18, r25|->r19, r25|->r20, r25|->r23, r25|->r24, r26|->r4, r26|->r5, r26|->r7, r26|->r8, r26|->r10, r26|->r13, r26|->r16, r26|->r18, r26|->r20, r26|->r23, r26|->r25, r27|->r1, r27|->r2, r27|->r3, r27|->r6, r27|->r8, r27|->r9, r27|->r11, r27|->r13, r27|->r16, r27|->r17, r27|->r20, r27|->r22, r27|->r23, r27|->r24, r28|->r2, r28|->r6, r28|->r9, r28|->r12, r28|->r15, r28|->r20, r28|->r22, r28|->r25, r28|->r27, r29|->r2, r29|->r3, r29|->r5, r29|->r6, r29|->r8, r29|->r10, r29|->r14, r29|->r15, r29|->r20, r29|->r22, r29|->r26, r29|->r27} &
    rules={rule0|->(rec(su:s11,re:r6,mo:pro,pr: 0,co:{c1,c0,c5,c9})), rule1|->(rec(su:s10,re:r14,mo:pro,pr: 2,co:{c1,c3,c4,c5,c7})), rule2|->(rec(su:s3,re:r3,mo:pro,pr: 3,co:{c7,c2})), rule3|->(rec(su:s20,re:r6,mo:per,pr: 0,co:{c1,c8,c3,c5,c7,c6,c4})), rule4|->(rec(su:s11,re:r11,mo:per,pr: 0,co:{c3,c9})), rule5|->(rec(su:s16,re:r4,mo:pro,pr: 4,co:{c9,c7,c5,c6,c0})), rule6|->(rec(su:s18,re:r29,mo:pro,pr: 0,co:{c6,c5,c3})), rule7|->(rec(su:s3,re:r15,mo:pro,pr: 2,co:{c1,c2,c3,c0,c5})), rule8|->(rec(su:s29,re:r5,mo:per,pr: 2,co:{c9,c7,c5})), rule9|->(rec(su:s22,re:r27,mo:per,pr: 2,co:{c4,c9,c6,c1,c7,c8,c5})), rule10|->(rec(su:s1,re:r22,mo:pro,pr: 0,co:{c6,c1,c8,c3})), rule11|->(rec(su:s7,re:r10,mo:pro,pr: 2,co:{c8}))}

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