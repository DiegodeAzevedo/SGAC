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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s3|->s0, s3|->s1, s3|->s2, s4|->s0, s5|->s1, s6|->s1, s6|->s2, s6|->s4, s7|->s0, s7|->s1, s8|->s0, s8|->s4, s8|->s5, s9|->s1, s9|->s3, s9|->s4, s9|->s7, s10|->s3, s10|->s4, s10|->s6, s10|->s7, s10|->s9, s11|->s2, s11|->s8, s12|->s0, s12|->s2, s12|->s3, s12|->s6, s12|->s7, s12|->s9, s13|->s2, s13|->s4, s13|->s5, s13|->s6, s13|->s9, s13|->s11, s13|->s12, s14|->s1, s14|->s4, s14|->s6, s14|->s7, s14|->s8, s14|->s10, s14|->s11, s14|->s13, s15|->s1, s15|->s2, s15|->s3, s15|->s4, s15|->s5, s15|->s6, s15|->s11, s15|->s14, s16|->s0, s16|->s3, s16|->s9, s16|->s10, s16|->s11, s16|->s12, s16|->s13, s17|->s1, s17|->s2, s17|->s4, s17|->s6, s17|->s9, s17|->s10, s17|->s12, s17|->s13, s18|->s0, s18|->s2, s18|->s3, s18|->s4, s18|->s5, s18|->s11, s18|->s12, s18|->s13, s18|->s16, s18|->s17, s19|->s4, s19|->s7, s19|->s9, s19|->s13, s19|->s14, s19|->s15, s19|->s18, s20|->s1, s20|->s3, s20|->s4, s20|->s5, s20|->s8, s20|->s10, s20|->s15, s20|->s18, s21|->s6, s21|->s7, s21|->s10, s21|->s11, s21|->s14, s21|->s15, s21|->s16, s21|->s19, s22|->s1, s22|->s2, s22|->s5, s22|->s7, s22|->s9, s22|->s13, s22|->s17, s22|->s18, s22|->s19, s23|->s1, s23|->s3, s23|->s6, s23|->s9, s23|->s12, s23|->s13, s23|->s14, s23|->s15, s23|->s17, s23|->s18, s23|->s20, s24|->s0, s24|->s2, s24|->s5, s24|->s6, s24|->s7, s24|->s10, s24|->s11, s24|->s13, s24|->s15, s24|->s16, s24|->s18, s24|->s19, s24|->s23, s25|->s0, s25|->s3, s25|->s8, s25|->s9, s25|->s11, s25|->s12, s25|->s13, s25|->s16, s25|->s19, s25|->s21, s25|->s22, s25|->s23, s26|->s2, s26|->s5, s26|->s6, s26|->s12, s26|->s15, s26|->s17, s26|->s18, s26|->s22, s26|->s24, s27|->s1, s27|->s2, s27|->s5, s27|->s9, s27|->s11, s27|->s13, s27|->s15, s27|->s21, s27|->s22, s27|->s23, s27|->s26} &
    e_res={r1|->r0, r3|->r0, r3|->r1, r4|->r0, r4|->r2, r4|->r3, r5|->r0, r5|->r1, r5|->r2, r5|->r3, r5|->r4, r6|->r0, r7|->r0, r7|->r1, r7|->r3, r7|->r4, r7|->r5, r8|->r0, r8|->r2, r8|->r4, r9|->r1, r9|->r5, r9|->r6, r9|->r8, r10|->r1, r10|->r3, r10|->r6, r10|->r7, r10|->r8, r11|->r2, r11|->r3, r11|->r4, r11|->r5, r11|->r7, r12|->r2, r12|->r3, r12|->r5, r12|->r11, r13|->r1, r13|->r7, r13|->r8, r13|->r11, r13|->r12, r14|->r0, r14|->r1, r14|->r2, r14|->r4, r14|->r5, r14|->r6, r14|->r8, r14|->r9, r14|->r10, r14|->r11, r14|->r12, r15|->r1, r15|->r3, r15|->r4, r15|->r5, r15|->r6, r15|->r7, r15|->r11, r15|->r13, r16|->r1, r16|->r6, r16|->r7, r16|->r8, r16|->r11, r16|->r13, r16|->r14, r17|->r2, r17|->r5, r17|->r6, r17|->r7, r17|->r8, r17|->r9, r17|->r11, r17|->r12, r17|->r13, r18|->r4, r18|->r6, r18|->r7, r18|->r8, r18|->r10, r18|->r12, r18|->r16, r19|->r0, r19|->r1, r19|->r3, r19|->r4, r19|->r5, r19|->r6, r19|->r7, r19|->r9, r19|->r10, r19|->r16, r19|->r17, r19|->r18, r20|->r6, r20|->r8, r20|->r13, r20|->r14, r20|->r15, r20|->r16, r20|->r17, r21|->r1, r21|->r7, r21|->r9, r21|->r10, r21|->r11, r21|->r18, r22|->r0, r22|->r1, r22|->r3, r22|->r6, r22|->r10, r22|->r11, r22|->r13, r22|->r17, r22|->r18, r22|->r19, r22|->r21, r23|->r3, r23|->r5, r23|->r10, r23|->r12, r23|->r14, r23|->r16, r23|->r17, r23|->r19, r24|->r0, r24|->r4, r24|->r5, r24|->r6, r24|->r10, r24|->r13, r24|->r16, r24|->r19, r24|->r21, r24|->r22, r25|->r3, r25|->r4, r25|->r5, r25|->r6, r25|->r8, r25|->r10, r25|->r13, r25|->r14, r25|->r16, r25|->r18, r25|->r19, r25|->r23, r25|->r24, r26|->r1, r26|->r2, r26|->r4, r26|->r6, r26|->r7, r26|->r8, r26|->r9, r26|->r10, r26|->r14, r26|->r16, r26|->r17, r26|->r18, r26|->r21, r26|->r22, r26|->r24, r26|->r25} &
    rules={rule0|->(rec(su:s16,re:r2,mo:per,pr: 2,co:{c3,c8,c5,c6,c9,c7})), rule1|->(rec(su:s10,re:r7,mo:pro,pr: 2,co:{c3,c8,c9,c1,c5,c0})), rule2|->(rec(su:s7,re:r10,mo:per,pr: 3,co:{c1,c2,c4})), rule3|->(rec(su:s15,re:r1,mo:pro,pr: 3,co:{c2,c1,c3,c7,c9,c4})), rule4|->(rec(su:s9,re:r12,mo:pro,pr: 4,co:{c6})), rule5|->(rec(su:s8,re:r11,mo:per,pr: 0,co:{c7})), rule6|->(rec(su:s17,re:r14,mo:per,pr: 4,co:{c7})), rule7|->(rec(su:s12,re:r7,mo:per,pr: 3,co:{c1,c5,c2,c0,c3})), rule8|->(rec(su:s18,re:r8,mo:pro,pr: 2,co:{c7})), rule9|->(rec(su:s11,re:r5,mo:pro,pr: 2,co:{c9,c6,c7,c8,c0,c1})), rule10|->(rec(su:s20,re:r12,mo:pro,pr: 3,co:{c8,c7,c0})), rule11|->(rec(su:s11,re:r5,mo:per,pr: 3,co:{c1,c8,c7,c2})), rule12|->(rec(su:s18,re:r1,mo:pro,pr: 2,co:{c7,c8,c0,c9,c4,c5}))}

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