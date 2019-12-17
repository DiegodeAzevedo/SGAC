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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26};
    /*rule type*/
    RULE_T={rule0, rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8, rule9, rule10, rule11, rule12};
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
    e_sub={s3|->s0, s3|->s1, s4|->s0, s4|->s1, s4|->s2, s4|->s3, s5|->s0, s6|->s0, s6|->s1, s6|->s2, s7|->s1, s7|->s4, s7|->s5, s7|->s6, s8|->s3, s8|->s5, s8|->s6, s9|->s4, s9|->s5, s9|->s6, s10|->s1, s10|->s2, s10|->s3, s10|->s6, s10|->s7, s10|->s8, s10|->s9, s11|->s0, s11|->s3, s11|->s5, s11|->s8, s11|->s9, s11|->s10, s12|->s0, s12|->s2, s12|->s3, s12|->s4, s12|->s6, s12|->s7, s12|->s11, s13|->s0, s13|->s3, s13|->s4, s13|->s10, s13|->s11, s13|->s12, s14|->s1, s14|->s3, s14|->s7, s14|->s9, s14|->s10, s14|->s12, s14|->s13, s15|->s0, s15|->s2, s15|->s3, s15|->s5, s15|->s7, s15|->s8, s15|->s9, s15|->s11, s15|->s13, s15|->s14, s16|->s2, s16|->s5, s16|->s6, s16|->s7, s16|->s10, s16|->s12, s16|->s14, s16|->s15, s17|->s2, s17|->s5, s17|->s6, s17|->s11, s17|->s12, s17|->s13, s17|->s14, s17|->s15, s17|->s16, s18|->s4, s18|->s5, s18|->s6, s18|->s7, s18|->s9, s18|->s10, s18|->s13, s18|->s14, s18|->s15, s18|->s16, s19|->s0, s19|->s2, s19|->s3, s19|->s4, s19|->s6, s19|->s7, s19|->s12, s20|->s0, s20|->s1, s20|->s2, s20|->s3, s20|->s4, s20|->s7, s20|->s8, s20|->s11, s20|->s12, s20|->s13, s20|->s15, s20|->s16, s20|->s17, s20|->s18, s20|->s19, s21|->s2, s21|->s4, s21|->s6, s21|->s7, s21|->s12, s21|->s13, s22|->s0, s22|->s3, s22|->s4, s22|->s7, s22|->s8, s22|->s9, s22|->s10, s22|->s11, s22|->s15, s22|->s16, s22|->s17, s22|->s18, s23|->s4, s23|->s7, s23|->s9, s23|->s10, s23|->s13, s23|->s14, s23|->s15, s23|->s17, s23|->s18, s23|->s20, s24|->s2, s24|->s6, s24|->s8, s24|->s9, s24|->s11, s24|->s16, s24|->s18, s24|->s20, s25|->s1, s25|->s2, s25|->s4, s25|->s5, s25|->s6, s25|->s7, s25|->s9, s25|->s10, s25|->s11, s25|->s12, s25|->s15, s25|->s19, s25|->s22, s25|->s23, s25|->s24, s26|->s0, s26|->s1, s26|->s3, s26|->s4, s26|->s7, s26|->s8, s26|->s9, s26|->s10, s26|->s11, s26|->s12, s26|->s13, s26|->s14, s26|->s15, s26|->s16, s26|->s17, s26|->s18, s26|->s19, s26|->s23, s27|->s1, s27|->s3, s27|->s5, s27|->s7, s27|->s8, s27|->s12, s27|->s13, s27|->s15, s27|->s16, s27|->s19, s27|->s21, s27|->s24} &
    e_res={r1|->r0, r2|->r1, r3|->r1, r4|->r0, r4|->r2, r5|->r1, r5|->r2, r5|->r4, r6|->r3, r7|->r1, r7|->r4, r8|->r0, r8|->r2, r8|->r3, r8|->r5, r8|->r6, r9|->r0, r9|->r3, r9|->r4, r9|->r5, r9|->r6, r10|->r0, r10|->r4, r11|->r1, r11|->r4, r11|->r5, r11|->r9, r11|->r10, r12|->r0, r12|->r2, r12|->r6, r12|->r9, r13|->r1, r13|->r3, r13|->r4, r13|->r5, r13|->r6, r13|->r7, r13|->r9, r13|->r10, r14|->r0, r14|->r1, r14|->r2, r14|->r3, r14|->r4, r14|->r5, r14|->r7, r14|->r8, r14|->r11, r14|->r13, r15|->r1, r15|->r3, r15|->r4, r15|->r6, r15|->r8, r15|->r13, r15|->r14, r16|->r2, r16|->r3, r16|->r4, r16|->r5, r16|->r6, r16|->r9, r16|->r10, r16|->r11, r16|->r13, r16|->r14, r16|->r15, r17|->r0, r17|->r1, r17|->r8, r17|->r9, r17|->r10, r17|->r11, r17|->r12, r17|->r14, r18|->r0, r18|->r1, r18|->r2, r18|->r4, r18|->r7, r18|->r9, r18|->r10, r18|->r11, r19|->r0, r19|->r2, r19|->r6, r19|->r7, r19|->r8, r19|->r10, r19|->r11, r19|->r12, r19|->r14, r19|->r15, r19|->r16, r20|->r1, r20|->r2, r20|->r3, r20|->r9, r20|->r10, r20|->r11, r20|->r13, r20|->r14, r20|->r15, r20|->r18, r20|->r19, r21|->r0, r21|->r6, r21|->r8, r21|->r12, r21|->r15, r21|->r16, r21|->r19, r22|->r0, r22|->r1, r22|->r3, r22|->r7, r22|->r9, r22|->r11, r22|->r12, r22|->r13, r22|->r15, r22|->r16, r22|->r17, r22|->r18, r23|->r0, r23|->r1, r23|->r4, r23|->r5, r23|->r7, r23|->r9, r23|->r10, r23|->r12, r23|->r18, r23|->r19, r23|->r20, r23|->r22, r24|->r1, r24|->r2, r24|->r3, r24|->r7, r24|->r8, r24|->r11, r24|->r13, r24|->r14, r24|->r22, r25|->r0, r25|->r2, r25|->r5, r25|->r9, r25|->r14, r25|->r15, r25|->r16, r25|->r17, r25|->r19, r26|->r3, r26|->r4, r26|->r6, r26|->r7, r26|->r8, r26|->r9, r26|->r12, r26|->r13, r26|->r14, r26|->r18, r26|->r19, r26|->r20, r26|->r25} &
    rules={rule0|->(rec(su:s8,re:r26,mo:pro,pr: 2,co:{c7,c6,c8,c5,c3,c2})), rule1|->(rec(su:s5,re:r23,mo:per,pr: 1,co:{c2,c0})), rule2|->(rec(su:s21,re:r26,mo:pro,pr: 1,co:{c3})), rule3|->(rec(su:s10,re:r26,mo:per,pr: 2,co:{c9,c1,c4,c2,c7,c5})), rule4|->(rec(su:s22,re:r24,mo:pro,pr: 0,co:{c7,c9,c2,c0,c6})), rule5|->(rec(su:s11,re:r5,mo:per,pr: 0,co:{c2,c5,c6,c1,c9,c7,c0,c3})), rule6|->(rec(su:s21,re:r16,mo:per,pr: 0,co:{c3,c1,c0,c9,c7,c2})), rule7|->(rec(su:s12,re:r16,mo:pro,pr: 4,co:{c8,c7})), rule8|->(rec(su:s19,re:r25,mo:per,pr: 1,co:{c9,c8,c7,c2,c0})), rule9|->(rec(su:s7,re:r21,mo:per,pr: 2,co:{c8,c5,c7,c0,c4,c2})), rule10|->(rec(su:s12,re:r6,mo:pro,pr: 0,co:{c8,c3,c7,c4,c2})), rule11|->(rec(su:s13,re:r8,mo:pro,pr: 3,co:{c2,c3,c6,c5,c4})), rule12|->(rec(su:s24,re:r8,mo:per,pr: 2,co:{c6,c2,c7}))}

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