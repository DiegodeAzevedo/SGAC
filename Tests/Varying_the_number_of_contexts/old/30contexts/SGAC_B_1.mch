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
    e_sub={s2|->s0, s3|->s0, s3|->s1, s3|->s2, s4|->s0, s4|->s1, s5|->s1, s5|->s2, s6|->s5, s7|->s1, s7|->s2, s7|->s4, s8|->s0, s8|->s1, s8|->s2, s8|->s4, s8|->s7, s9|->s1, s9|->s4, s10|->s0, s10|->s3, s10|->s5, s10|->s6, s10|->s7, s10|->s8, s10|->s9, s11|->s3, s11|->s4, s11|->s6, s11|->s7, s11|->s8, s11|->s9, s12|->s0, s12|->s3, s12|->s4, s12|->s5, s12|->s9, s13|->s11, s13|->s12, s14|->s0, s14|->s1, s14|->s3, s14|->s4, s14|->s5, s14|->s10, s15|->s0, s15|->s2, s15|->s3, s15|->s5, s15|->s6, s15|->s7, s15|->s9, s15|->s11, s15|->s13, s16|->s1, s16|->s3, s16|->s5, s16|->s7, s16|->s8, s16|->s10, s16|->s11, s16|->s12, s16|->s14, s16|->s15, s17|->s5, s17|->s7, s17|->s8, s17|->s10, s17|->s11, s17|->s12, s18|->s1, s18|->s2, s18|->s3, s18|->s5, s18|->s7, s18|->s8, s18|->s9, s18|->s12, s18|->s13, s18|->s14, s18|->s15, s18|->s17, s19|->s0, s19|->s1, s19|->s4, s19|->s5, s19|->s12, s19|->s18, s20|->s1, s20|->s5, s20|->s6, s20|->s7, s20|->s8, s20|->s9, s20|->s10, s20|->s11, s20|->s12, s20|->s13, s20|->s18, s21|->s2, s21|->s3, s21|->s6, s21|->s7, s21|->s9, s21|->s13, s21|->s14, s21|->s15, s21|->s17, s21|->s18, s22|->s1, s22|->s2, s22|->s7, s22|->s8, s22|->s10, s22|->s14, s22|->s15, s22|->s18, s22|->s19, s22|->s20, s23|->s1, s23|->s2, s23|->s5, s23|->s6, s23|->s10, s23|->s12, s23|->s14, s23|->s16, s23|->s17, s23|->s19, s23|->s20, s24|->s2, s24|->s5, s24|->s8, s24|->s10, s24|->s11, s24|->s12, s24|->s14, s24|->s15, s24|->s16, s24|->s23, s25|->s0, s25|->s3, s25|->s4, s25|->s5, s25|->s8, s25|->s9, s25|->s10, s25|->s14, s25|->s15, s25|->s17, s25|->s18, s25|->s20, s25|->s22, s26|->s0, s26|->s1, s26|->s3, s26|->s4, s26|->s5, s26|->s6, s26|->s9, s26|->s12, s26|->s13, s26|->s14, s26|->s15, s26|->s18, s26|->s19, s26|->s20, s26|->s21, s26|->s23, s27|->s0, s27|->s1, s27|->s2, s27|->s5, s27|->s7, s27|->s8, s27|->s10, s27|->s13, s27|->s14, s27|->s17, s27|->s18, s27|->s19, s27|->s21, s27|->s22, s27|->s23, s27|->s25, s27|->s26, s28|->s0, s28|->s1, s28|->s3, s28|->s5, s28|->s7, s28|->s8, s28|->s12, s28|->s16, s28|->s17, s28|->s18, s28|->s19, s28|->s20, s28|->s24, s28|->s25, s28|->s27, s29|->s1, s29|->s3, s29|->s4, s29|->s6, s29|->s7, s29|->s9, s29|->s10, s29|->s14, s29|->s15, s29|->s19, s29|->s21, s29|->s24, s29|->s25, s29|->s27, s29|->s28} &
    e_res={r1|->r0, r3|->r0, r3|->r2, r4|->r1, r4|->r2, r4|->r3, r5|->r0, r5|->r2, r5|->r4, r6|->r0, r6|->r1, r7|->r4, r7|->r5, r8|->r2, r8|->r3, r8|->r4, r8|->r5, r8|->r6, r8|->r7, r9|->r6, r9|->r8, r10|->r3, r10|->r5, r10|->r6, r11|->r1, r11|->r2, r11|->r4, r11|->r5, r11|->r8, r11|->r9, r11|->r10, r12|->r0, r12|->r4, r12|->r11, r13|->r0, r13|->r1, r13|->r4, r13|->r5, r13|->r6, r13|->r10, r13|->r11, r14|->r0, r14|->r2, r14|->r3, r14|->r4, r14|->r8, r14|->r10, r14|->r13, r15|->r1, r15|->r3, r15|->r4, r15|->r6, r15|->r7, r15|->r10, r15|->r12, r15|->r13, r16|->r2, r16|->r3, r16|->r4, r16|->r9, r16|->r13, r16|->r14, r17|->r1, r17|->r3, r17|->r5, r17|->r6, r17|->r8, r17|->r10, r17|->r11, r17|->r12, r17|->r15, r18|->r1, r18|->r2, r18|->r3, r18|->r10, r18|->r11, r18|->r12, r18|->r13, r18|->r16, r18|->r17, r19|->r0, r19|->r7, r19|->r8, r19|->r11, r19|->r14, r20|->r0, r20|->r3, r20|->r7, r20|->r11, r20|->r13, r20|->r15, r20|->r17, r20|->r19, r21|->r1, r21|->r2, r21|->r5, r21|->r6, r21|->r9, r21|->r11, r21|->r13, r21|->r15, r21|->r17, r21|->r19, r21|->r20, r22|->r1, r22|->r2, r22|->r4, r22|->r7, r22|->r8, r22|->r10, r22|->r13, r22|->r14, r22|->r17, r22|->r18, r22|->r19, r22|->r20, r22|->r21, r23|->r2, r23|->r6, r23|->r7, r23|->r11, r23|->r17, r23|->r18, r23|->r20, r23|->r21, r24|->r3, r24|->r4, r24|->r5, r24|->r8, r24|->r10, r24|->r12, r24|->r15, r24|->r16, r24|->r18, r25|->r0, r25|->r5, r25|->r6, r25|->r10, r25|->r13, r25|->r14, r25|->r15, r25|->r19, r25|->r20, r26|->r2, r26|->r3, r26|->r5, r26|->r7, r26|->r8, r26|->r10, r26|->r11, r26|->r12, r26|->r13, r26|->r14, r26|->r17, r26|->r18, r26|->r19, r26|->r21, r26|->r23, r27|->r4, r27|->r5, r27|->r7, r27|->r8, r27|->r10, r27|->r11, r27|->r14, r27|->r19, r27|->r20, r27|->r23, r27|->r24, r27|->r26, r28|->r0, r28|->r1, r28|->r2, r28|->r4, r28|->r6, r28|->r7, r28|->r10, r28|->r13, r28|->r16, r28|->r17, r28|->r18, r28|->r19, r28|->r20, r28|->r22, r28|->r27, r29|->r2, r29|->r3, r29|->r5, r29|->r9, r29|->r11, r29|->r15, r29|->r17, r29|->r18, r29|->r23, r29|->r24, r29|->r25, r29|->r26, r29|->r28} &
    rules={rule0|->(rec(su:s9,re:r11,mo:pro,pr: 3,co:{c4,c7,c6})), rule1|->(rec(su:s14,re:r7,mo:pro,pr: 1,co:{c5,c1,c0})), rule2|->(rec(su:s21,re:r17,mo:per,pr: 3,co:{c3,c7,c4})), rule3|->(rec(su:s16,re:r24,mo:per,pr: 1,co:{c0,c9,c2,c7,c8,c1})), rule4|->(rec(su:s5,re:r29,mo:pro,pr: 0,co:{c8,c6,c4})), rule5|->(rec(su:s25,re:r22,mo:pro,pr: 4,co:{c8,c7,c2,c6,c0,c3,c9})), rule6|->(rec(su:s5,re:r24,mo:per,pr: 4,co:{c1,c0})), rule7|->(rec(su:s9,re:r10,mo:per,pr: 4,co:{c7,c4})), rule8|->(rec(su:s3,re:r23,mo:per,pr: 3,co:{c0,c6,c2,c1,c7})), rule9|->(rec(su:s15,re:r8,mo:pro,pr: 4,co:{c8,c3,c9,c4,c1,c0,c2})), rule10|->(rec(su:s4,re:r28,mo:pro,pr: 2,co:{c2,c4,c8,c0,c1,c3,c5})), rule11|->(rec(su:s25,re:r16,mo:pro,pr: 1,co:{c0,c3,c1,c6}))}

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