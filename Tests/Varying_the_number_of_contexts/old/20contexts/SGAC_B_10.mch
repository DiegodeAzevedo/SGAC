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
    e_sub={s1|->s0, s2|->s0, s2|->s1, s4|->s2, s5|->s1, s5|->s3, s5|->s4, s6|->s2, s6|->s5, s8|->s0, s8|->s6, s9|->s0, s9|->s3, s9|->s4, s9|->s5, s9|->s8, s10|->s1, s10|->s6, s11|->s0, s11|->s1, s11|->s2, s11|->s4, s11|->s5, s11|->s10, s12|->s3, s12|->s4, s12|->s6, s12|->s7, s12|->s8, s12|->s10, s12|->s11, s13|->s1, s13|->s2, s13|->s6, s13|->s8, s13|->s9, s13|->s10, s13|->s12, s14|->s1, s14|->s2, s14|->s3, s14|->s5, s14|->s6, s14|->s7, s14|->s8, s14|->s9, s14|->s10, s15|->s5, s15|->s6, s15|->s7, s15|->s8, s15|->s14, s16|->s1, s16|->s4, s16|->s5, s16|->s6, s16|->s9, s16|->s12, s16|->s13, s17|->s1, s17|->s2, s17|->s5, s17|->s6, s17|->s9, s17|->s12, s18|->s4, s18|->s7, s18|->s9, s18|->s14, s18|->s15, s18|->s16, s19|->s0, s19|->s4, s19|->s7, s19|->s8, s19|->s9, s19|->s12, s19|->s16, s19|->s18, s20|->s1, s20|->s2, s20|->s3, s20|->s4, s20|->s5, s20|->s7, s20|->s13, s20|->s15, s20|->s17, s20|->s19, s21|->s0, s21|->s2, s21|->s3, s21|->s4, s21|->s5, s21|->s9, s21|->s11, s21|->s12, s21|->s13, s22|->s0, s22|->s2, s22|->s3, s22|->s6, s22|->s10, s22|->s11, s22|->s18, s23|->s0, s23|->s2, s23|->s4, s23|->s6, s23|->s10, s23|->s12, s23|->s13, s23|->s14, s23|->s15, s23|->s16, s23|->s17, s23|->s18, s23|->s22, s24|->s0, s24|->s1, s24|->s2, s24|->s3, s24|->s4, s24|->s5, s24|->s9, s24|->s10, s24|->s11, s24|->s12, s24|->s13, s24|->s14, s24|->s15, s24|->s17, s24|->s19, s24|->s20, s24|->s21, s25|->s1, s25|->s5, s25|->s7, s25|->s9, s25|->s10, s25|->s12, s25|->s15, s25|->s16, s25|->s18, s25|->s19, s25|->s20, s26|->s0, s26|->s2, s26|->s6, s26|->s7, s26|->s9, s26|->s10, s26|->s12, s26|->s17, s26|->s19, s26|->s21, s26|->s23, s26|->s24, s27|->s0, s27|->s2, s27|->s5, s27|->s6, s27|->s8, s27|->s9, s27|->s11, s27|->s12, s27|->s15, s27|->s16, s27|->s18, s27|->s20, s27|->s21, s27|->s25, s27|->s26, s28|->s1, s28|->s2, s28|->s3, s28|->s5, s28|->s6, s28|->s8, s28|->s11, s28|->s13, s28|->s14, s28|->s15, s28|->s18, s28|->s19, s28|->s20, s28|->s23, s28|->s25, s28|->s27, s29|->s0, s29|->s2, s29|->s4, s29|->s7, s29|->s9, s29|->s10, s29|->s11, s29|->s12, s29|->s18, s29|->s19, s29|->s20, s29|->s23, s29|->s28} &
    e_res={r2|->r1, r3|->r1, r5|->r0, r5|->r2, r5|->r3, r6|->r0, r6|->r2, r7|->r0, r7|->r1, r7|->r2, r7|->r4, r7|->r5, r8|->r0, r8|->r1, r8|->r3, r8|->r4, r8|->r6, r8|->r7, r9|->r1, r9|->r2, r9|->r3, r9|->r4, r9|->r8, r10|->r0, r10|->r1, r10|->r2, r10|->r9, r11|->r4, r11|->r8, r11|->r10, r12|->r0, r12|->r1, r12|->r5, r12|->r6, r12|->r8, r12|->r9, r12|->r10, r13|->r0, r13|->r2, r13|->r3, r13|->r5, r13|->r6, r13|->r9, r13|->r10, r13|->r12, r14|->r2, r14|->r3, r14|->r5, r14|->r6, r14|->r7, r14|->r9, r14|->r13, r15|->r0, r15|->r3, r15|->r4, r15|->r8, r15|->r10, r15|->r12, r15|->r13, r15|->r14, r16|->r2, r16|->r4, r16|->r6, r16|->r13, r16|->r15, r17|->r0, r17|->r1, r17|->r2, r17|->r5, r17|->r6, r17|->r7, r17|->r8, r17|->r9, r17|->r10, r17|->r11, r17|->r14, r17|->r16, r18|->r7, r18|->r8, r18|->r9, r18|->r10, r18|->r11, r18|->r12, r18|->r13, r18|->r15, r18|->r16, r18|->r17, r19|->r1, r19|->r5, r19|->r8, r19|->r10, r19|->r11, r19|->r13, r19|->r16, r20|->r1, r20|->r2, r20|->r4, r20|->r5, r20|->r6, r20|->r10, r20|->r11, r20|->r12, r20|->r13, r20|->r15, r20|->r16, r20|->r17, r20|->r18, r20|->r19, r21|->r0, r21|->r1, r21|->r2, r21|->r3, r21|->r5, r21|->r8, r21|->r9, r21|->r10, r21|->r11, r21|->r13, r21|->r14, r21|->r17, r21|->r18, r22|->r6, r22|->r10, r22|->r12, r22|->r13, r22|->r15, r22|->r16, r22|->r17, r22|->r19, r23|->r0, r23|->r5, r23|->r8, r23|->r12, r23|->r13, r23|->r14, r23|->r15, r23|->r16, r23|->r19, r24|->r1, r24|->r2, r24|->r5, r24|->r7, r24|->r8, r24|->r11, r24|->r13, r24|->r14, r24|->r15, r24|->r18, r24|->r19, r24|->r20, r24|->r23, r25|->r3, r25|->r5, r25|->r6, r25|->r7, r25|->r11, r25|->r15, r25|->r18, r25|->r22, r26|->r0, r26|->r1, r26|->r2, r26|->r3, r26|->r5, r26|->r8, r26|->r10, r26|->r15, r26|->r16, r26|->r17, r26|->r18, r26|->r20, r27|->r4, r27|->r10, r27|->r12, r27|->r13, r27|->r15, r27|->r17, r27|->r19, r27|->r21, r27|->r23, r27|->r25, r28|->r1, r28|->r2, r28|->r5, r28|->r8, r28|->r9, r28|->r10, r28|->r12, r28|->r16, r28|->r17, r28|->r18, r28|->r19, r28|->r24, r28|->r26, r29|->r0, r29|->r1, r29|->r3, r29|->r5, r29|->r6, r29|->r8, r29|->r9, r29|->r10, r29|->r13, r29|->r16, r29|->r17, r29|->r18, r29|->r20, r29|->r22, r29|->r23, r29|->r24, r29|->r28} &
    rules={rule0|->(rec(su:s23,re:r28,mo:per,pr: 1,co:{c6,c2,c3,c8,c4,c9,c7})), rule1|->(rec(su:s20,re:r19,mo:pro,pr: 0,co:{c9,c8,c6,c3,c1,c7})), rule2|->(rec(su:s16,re:r0,mo:pro,pr: 2,co:{c1,c3,c7,c0,c4})), rule3|->(rec(su:s25,re:r2,mo:pro,pr: 1,co:{c6,c9,c7})), rule4|->(rec(su:s8,re:r23,mo:pro,pr: 4,co:{c9,c2,c3})), rule5|->(rec(su:s23,re:r26,mo:per,pr: 0,co:{c3,c4,c9,c7,c5,c8,c6,c0})), rule6|->(rec(su:s23,re:r16,mo:pro,pr: 0,co:{c9,c7,c2,c8,c5})), rule7|->(rec(su:s20,re:r25,mo:per,pr: 4,co:{c3,c5,c6,c2,c1})), rule8|->(rec(su:s23,re:r1,mo:pro,pr: 1,co:{c7,c5})), rule9|->(rec(su:s29,re:r1,mo:pro,pr: 1,co:{c5,c1,c3,c2})), rule10|->(rec(su:s13,re:r19,mo:pro,pr: 1,co:{c1,c4})), rule11|->(rec(su:s0,re:r11,mo:per,pr: 4,co:{c5}))}

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