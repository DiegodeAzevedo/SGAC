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
    e_sub={s1|->s0, s3|->s0, s4|->s0, s4|->s2, s4|->s3, s5|->s0, s5|->s3, s5|->s4, s6|->s1, s6|->s4, s6|->s5, s7|->s0, s7|->s1, s7|->s2, s7|->s4, s7|->s5, s7|->s6, s8|->s0, s8|->s4, s8|->s5, s9|->s1, s9|->s2, s9|->s3, s9|->s4, s10|->s1, s10|->s4, s10|->s8, s10|->s9, s11|->s0, s11|->s1, s11|->s3, s11|->s4, s11|->s8, s11|->s9, s11|->s10, s12|->s0, s12|->s1, s12|->s2, s12|->s5, s12|->s8, s12|->s9, s12|->s10, s12|->s11, s13|->s2, s13|->s4, s13|->s9, s13|->s11, s14|->s1, s14|->s2, s14|->s3, s14|->s6, s14|->s10, s14|->s11, s14|->s13, s15|->s3, s15|->s4, s15|->s6, s15|->s7, s15|->s8, s15|->s10, s15|->s11, s15|->s14, s16|->s0, s16|->s1, s16|->s2, s16|->s5, s16|->s6, s16|->s7, s16|->s9, s16|->s11, s16|->s15, s17|->s0, s17|->s1, s17|->s2, s17|->s4, s17|->s5, s17|->s8, s17|->s10, s17|->s13, s17|->s14, s17|->s16, s18|->s0, s18|->s1, s18|->s2, s18|->s4, s18|->s5, s18|->s6, s18|->s7, s18|->s8, s18|->s11, s18|->s12, s18|->s17, s19|->s6, s19|->s7, s19|->s8, s19|->s9, s19|->s11, s19|->s14, s19|->s15, s19|->s18, s20|->s1, s20|->s5, s20|->s12, s20|->s14, s20|->s17, s20|->s18, s21|->s2, s21|->s3, s21|->s5, s21|->s7, s21|->s8, s21|->s9, s21|->s10, s21|->s11, s21|->s13, s21|->s15, s21|->s16, s21|->s17, s21|->s18, s22|->s1, s22|->s2, s22|->s3, s22|->s4, s22|->s5, s22|->s8, s22|->s11, s22|->s13, s22|->s14, s22|->s16, s22|->s17, s22|->s19, s23|->s0, s23|->s1, s23|->s4, s23|->s5, s23|->s6, s23|->s9, s23|->s10, s23|->s13, s23|->s14, s23|->s17, s23|->s19, s23|->s20, s24|->s0, s24|->s2, s24|->s3, s24|->s5, s24|->s6, s24|->s10, s24|->s12, s24|->s20, s24|->s23, s25|->s2, s25|->s3, s25|->s4, s25|->s5, s25|->s10, s25|->s12, s25|->s13, s25|->s16, s25|->s19, s25|->s24, s26|->s0, s26|->s1, s26|->s2, s26|->s3, s26|->s7, s26|->s11, s26|->s12, s26|->s13, s26|->s14, s26|->s20, s26|->s25, s27|->s0, s27|->s3, s27|->s4, s27|->s5, s27|->s8, s27|->s9, s27|->s13, s27|->s14, s27|->s15, s27|->s16, s27|->s17, s27|->s22, s27|->s26, s28|->s1, s28|->s6, s28|->s7, s28|->s8, s28|->s9, s28|->s10, s28|->s12, s28|->s16, s28|->s17, s28|->s18, s28|->s19, s28|->s22, s28|->s23, s28|->s24, s28|->s25, s29|->s0, s29|->s1, s29|->s4, s29|->s6, s29|->s8, s29|->s11, s29|->s18, s29|->s20, s29|->s21, s29|->s24, s29|->s25, s29|->s26} &
    e_res={r1|->r0, r2|->r1, r4|->r1, r4|->r2, r5|->r2, r6|->r2, r7|->r1, r7|->r2, r7|->r4, r7|->r5, r8|->r3, r8|->r4, r8|->r6, r8|->r7, r9|->r3, r9|->r5, r9|->r8, r10|->r3, r10|->r8, r10|->r9, r11|->r1, r11|->r2, r11|->r3, r11|->r4, r11|->r5, r11|->r6, r11|->r7, r11|->r8, r11|->r9, r12|->r0, r12|->r2, r12|->r3, r12|->r4, r12|->r6, r12|->r7, r12|->r10, r12|->r11, r13|->r2, r13|->r4, r13|->r7, r13|->r8, r13|->r9, r13|->r11, r13|->r12, r14|->r0, r14|->r1, r14|->r2, r14|->r4, r14|->r5, r14|->r8, r14|->r9, r14|->r10, r14|->r11, r14|->r12, r15|->r0, r15|->r2, r15|->r4, r15|->r6, r15|->r7, r15|->r9, r15|->r10, r15|->r13, r16|->r0, r16|->r3, r16|->r4, r16|->r5, r16|->r12, r16|->r13, r16|->r14, r17|->r2, r17|->r5, r17|->r7, r17|->r8, r17|->r10, r17|->r11, r17|->r12, r17|->r13, r18|->r0, r18|->r1, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r8, r18|->r9, r18|->r13, r18|->r15, r18|->r17, r19|->r0, r19|->r1, r19|->r2, r19|->r3, r19|->r4, r19|->r6, r19|->r7, r19|->r8, r19|->r13, r19|->r14, r20|->r0, r20|->r2, r20|->r6, r20|->r8, r20|->r9, r20|->r10, r20|->r13, r20|->r15, r20|->r19, r21|->r1, r21|->r2, r21|->r3, r21|->r4, r21|->r9, r21|->r17, r21|->r18, r21|->r19, r22|->r0, r22|->r3, r22|->r4, r22|->r5, r22|->r6, r22|->r7, r22|->r10, r22|->r11, r22|->r12, r22|->r15, r22|->r16, r22|->r17, r22|->r20, r23|->r0, r23|->r2, r23|->r4, r23|->r5, r23|->r12, r23|->r13, r23|->r14, r23|->r18, r23|->r20, r23|->r22, r24|->r0, r24|->r5, r24|->r6, r24|->r7, r24|->r9, r24|->r13, r24|->r15, r24|->r16, r24|->r19, r24|->r21, r24|->r22, r24|->r23, r25|->r1, r25|->r2, r25|->r4, r25|->r6, r25|->r8, r25|->r10, r25|->r12, r25|->r17, r25|->r18, r25|->r19, r25|->r22, r25|->r24, r26|->r3, r26|->r4, r26|->r5, r26|->r6, r26|->r7, r26|->r9, r26|->r10, r26|->r15, r26|->r17, r26|->r18, r26|->r19, r26|->r20, r26|->r21, r26|->r22, r26|->r23, r26|->r24, r27|->r7, r27|->r8, r27|->r9, r27|->r10, r27|->r11, r27|->r12, r27|->r13, r27|->r15, r27|->r17, r27|->r19, r27|->r22, r27|->r23, r28|->r0, r28|->r1, r28|->r8, r28|->r10, r28|->r13, r28|->r15, r28|->r16, r28|->r17, r28|->r19, r28|->r21, r28|->r24, r28|->r26, r28|->r27, r29|->r0, r29|->r1, r29|->r2, r29|->r3, r29|->r4, r29|->r5, r29|->r7, r29|->r8, r29|->r10, r29|->r15, r29|->r19, r29|->r20, r29|->r21, r29|->r26, r29|->r27, r29|->r28} &
    rules={rule0|->(rec(su:s25,re:r16,mo:pro,pr: 3,co:{c6})), rule1|->(rec(su:s1,re:r26,mo:per,pr: 1,co:{c6})), rule2|->(rec(su:s3,re:r7,mo:pro,pr: 0,co:{c4})), rule3|->(rec(su:s22,re:r20,mo:per,pr: 2,co:{c5,c2,c4,c9,c1,c6,c7})), rule4|->(rec(su:s26,re:r11,mo:pro,pr: 4,co:{c9,c3,c8,c2})), rule5|->(rec(su:s29,re:r0,mo:pro,pr: 1,co:{c0,c5,c3,c4,c8,c9,c1})), rule6|->(rec(su:s4,re:r29,mo:pro,pr: 2,co:{c4,c0,c2,c1,c5})), rule7|->(rec(su:s11,re:r9,mo:pro,pr: 4,co:{c6,c4,c2})), rule8|->(rec(su:s8,re:r12,mo:per,pr: 4,co:{c6})), rule9|->(rec(su:s11,re:r3,mo:per,pr: 2,co:{c1,c2})), rule10|->(rec(su:s24,re:r14,mo:pro,pr: 2,co:{c2,c3,c4,c0,c1,c5})), rule11|->(rec(su:s29,re:r12,mo:pro,pr: 0,co:{c4,c7,c5,c3,c1,c2}))}

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