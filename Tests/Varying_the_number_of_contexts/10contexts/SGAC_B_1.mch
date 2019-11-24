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
    e_sub={s9|->s0, s9|->s6, s9|->s8, s8|->s1, s8|->s2, s8|->s4, s8|->s6, s8|->s7, s3|->s2, s2|->s0, s1|->s0, s7|->s0, s7|->s1, s7|->s2, s7|->s5, s6|->s0, s6|->s2, s6|->s3, s5|->s2, s5|->s3, s19|->s2, s19|->s5, s19|->s6, s19|->s9, s19|->s10, s19|->s11, s19|->s14, s19|->s15, s19|->s17, s19|->s18, s18|->s0, s18|->s1, s18|->s2, s18|->s3, s18|->s5, s18|->s6, s18|->s8, s18|->s9, s18|->s10, s18|->s11, s18|->s14, s18|->s17, s13|->s0, s13|->s1, s13|->s3, s13|->s4, s13|->s10, s13|->s11, s13|->s12, s12|->s3, s12|->s4, s12|->s7, s12|->s9, s11|->s3, s11|->s4, s11|->s5, s11|->s6, s11|->s7, s11|->s8, s11|->s10, s10|->s0, s10|->s4, s10|->s5, s10|->s6, s10|->s7, s10|->s8, s17|->s0, s17|->s1, s17|->s4, s17|->s5, s17|->s6, s17|->s7, s17|->s8, s17|->s10, s17|->s11, s17|->s12, s17|->s13, s17|->s15, s16|->s0, s16|->s7, s16|->s8, s16|->s10, s16|->s11, s16|->s13, s16|->s15, s15|->s1, s15|->s2, s15|->s3, s15|->s8, s15|->s9, s15|->s11, s15|->s12, s15|->s13, s15|->s14, s14|->s0, s14|->s1, s14|->s2, s14|->s3, s14|->s4, s14|->s7, s14|->s12, s14|->s13, s22|->s1, s22|->s4, s22|->s5, s22|->s10, s22|->s17, s22|->s21, s23|->s1, s23|->s2, s23|->s4, s23|->s5, s23|->s7, s23|->s8, s23|->s9, s23|->s11, s23|->s14, s23|->s15, s23|->s16, s23|->s18, s23|->s20, s23|->s22, s20|->s2, s20|->s3, s20|->s4, s20|->s5, s20|->s9, s20|->s10, s20|->s13, s20|->s15, s20|->s17, s20|->s19, s21|->s1, s21|->s3, s21|->s9, s21|->s12, s21|->s13, s21|->s14, s21|->s15, s21|->s17, s21|->s18, s21|->s19, s26|->s0, s26|->s6, s26|->s7, s26|->s8, s26|->s9, s26|->s13, s26|->s14, s26|->s15, s26|->s17, s26|->s18, s26|->s19, s26|->s21, s26|->s22, s26|->s24, s26|->s25, s27|->s0, s27|->s3, s27|->s5, s27|->s7, s27|->s9, s27|->s10, s27|->s12, s27|->s13, s27|->s14, s27|->s17, s27|->s18, s27|->s19, s27|->s20, s27|->s23, s24|->s3, s24|->s7, s24|->s14, s24|->s20, s24|->s22, s25|->s0, s25|->s1, s25|->s2, s25|->s3, s25|->s4, s25|->s8, s25|->s10, s25|->s12, s25|->s13, s25|->s14, s25|->s20, s25|->s21, s25|->s22, s25|->s24, s28|->s1, s28|->s2, s28|->s4, s28|->s5, s28|->s9, s28|->s14, s28|->s16, s28|->s17, s28|->s18, s28|->s21, s28|->s22, s28|->s23, s28|->s26, s28|->s27, s29|->s0, s29|->s1, s29|->s2, s29|->s6, s29|->s8, s29|->s10, s29|->s11, s29|->s14, s29|->s17, s29|->s19, s29|->s21, s29|->s22} &
    e_res={r29|->r6, r29|->r9, r29|->r10, r29|->r12, r29|->r14, r29|->r15, r29|->r18, r29|->r24, r29|->r28, r28|->r2, r28|->r5, r28|->r6, r28|->r7, r28|->r8, r28|->r13, r28|->r14, r28|->r17, r28|->r18, r28|->r21, r28|->r22, r28|->r24, r28|->r26, r28|->r27, r27|->r1, r27|->r3, r27|->r6, r27|->r7, r27|->r9, r27|->r10, r27|->r11, r27|->r15, r27|->r17, r27|->r19, r27|->r22, r27|->r23, r27|->r24, r27|->r25, r27|->r26, r26|->r1, r26|->r2, r26|->r3, r26|->r4, r26|->r5, r26|->r6, r26|->r9, r26|->r11, r26|->r13, r26|->r21, r26|->r22, r26|->r24, r25|->r3, r25|->r6, r25|->r8, r25|->r9, r25|->r11, r25|->r12, r25|->r14, r25|->r18, r25|->r22, r25|->r23, r25|->r24, r24|->r2, r24|->r4, r24|->r6, r24|->r10, r24|->r12, r24|->r14, r24|->r18, r24|->r21, r23|->r0, r23|->r2, r23|->r5, r23|->r6, r23|->r7, r23|->r11, r23|->r12, r23|->r19, r23|->r20, r22|->r1, r22|->r2, r22|->r4, r22|->r6, r22|->r7, r22|->r8, r22|->r11, r22|->r13, r22|->r14, r22|->r15, r22|->r18, r22|->r19, r22|->r20, r22|->r21, r21|->r0, r21|->r1, r21|->r2, r21|->r3, r21|->r4, r21|->r7, r21|->r9, r21|->r11, r21|->r13, r21|->r14, r21|->r15, r20|->r0, r20|->r3, r20|->r8, r20|->r9, r20|->r10, r20|->r11, r20|->r14, r16|->r0, r16|->r4, r16|->r6, r16|->r8, r16|->r9, r16|->r12, r16|->r14, r17|->r2, r17|->r3, r17|->r4, r17|->r9, r17|->r11, r17|->r12, r17|->r15, r17|->r16, r14|->r0, r14|->r2, r14|->r3, r14|->r4, r14|->r5, r14|->r8, r14|->r10, r14|->r11, r14|->r12, r14|->r13, r15|->r1, r15|->r2, r15|->r3, r15|->r5, r15|->r7, r15|->r8, r15|->r12, r15|->r13, r12|->r1, r12|->r4, r12|->r5, r12|->r6, r12|->r8, r12|->r9, r13|->r1, r13|->r3, r13|->r6, r13|->r11, r10|->r0, r10|->r1, r10|->r4, r10|->r5, r10|->r7, r10|->r8, r11|->r0, r11|->r2, r11|->r3, r11|->r5, r11|->r7, r18|->r0, r18|->r1, r18|->r2, r18|->r3, r18|->r5, r18|->r7, r18|->r8, r18|->r12, r18|->r13, r18|->r16, r18|->r17, r19|->r4, r19|->r6, r19|->r7, r19|->r8, r19|->r9, r19|->r10, r19|->r15, r19|->r16, r19|->r17, r4|->r1, r5|->r0, r5|->r1, r6|->r3, r6|->r5, r7|->r0, r7|->r2, r7|->r4, r7|->r5, r7|->r6, r1|->r0, r3|->r0, r3|->r1, r8|->r0, r8|->r4, r8|->r5, r8|->r6, r9|->r1, r9|->r2, r9|->r3, r9|->r4, r9|->r7, r9|->r8} &
    rules={rule9|->(rec(su:s22,re:r2,mo:pro,pr: 4,co:{c0,c1,c3,c2,c7,c8,c6,c5})), rule8|->(rec(su:s27,re:r25,mo:per,pr: 4,co:{c9,c8})), rule3|->(rec(su:s0,re:r21,mo:pro,pr: 0,co:{c7,c5,c1,c9,c6})), rule2|->(rec(su:s24,re:r1,mo:pro,pr: 3,co:{c5,c4,c9,c8})), rule1|->(rec(su:s27,re:r16,mo:pro,pr: 3,co:{c9,c5,c0,c3,c7,c4,c1})), rule0|->(rec(su:s6,re:r1,mo:pro,pr: 4,co:{c7,c0,c8,c3,c4})), rule7|->(rec(su:s29,re:r25,mo:per,pr: 0,co:{c0,c1,c2,c7,c3})), rule6|->(rec(su:s0,re:r26,mo:pro,pr: 3,co:{c7,c3,c5,c6,c2,c9})), rule5|->(rec(su:s2,re:r20,mo:pro,pr: 0,co:{c2,c0,c6,c8,c9})), rule4|->(rec(su:s23,re:r4,mo:per,pr: 1,co:{c3,c5,c1,c4,c7})), rule11|->(rec(su:s22,re:r16,mo:per,pr: 0,co:{c6,c3,c2})), rule10|->(rec(su:s7,re:r17,mo:per,pr: 4,co:{c5,c4,c6,c3,c2,c1,c8}))}

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