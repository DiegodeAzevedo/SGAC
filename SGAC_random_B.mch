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
    CONTEXT={c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12};
    /*subject vertex type*/
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25};
    /*rule type*/
    RULE_T={rule0, rule1, rule2};
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
    e_sub={s1|->s0, s2|->s1, s3|->s1, s3|->s2, s4|->s0, s4|->s1, s5|->s1, s5|->s3, s6|->s0, s6|->s3, s6|->s4, s6|->s5, s7|->s0, s7|->s2, s7|->s5, s8|->s0, s8|->s1, s8|->s4, s8|->s7, s9|->s0, s10|->s0, s10|->s1, s10|->s3, s10|->s4, s10|->s5, s11|->s1, s11|->s3, s11|->s4, s11|->s7, s11|->s9, s11|->s10, s12|->s2, s12|->s4, s12|->s9, s12|->s10, s12|->s11, s13|->s4, s13|->s6, s13|->s12, s14|->s0, s14|->s1, s14|->s4, s14|->s7, s14|->s8, s14|->s9, s14|->s10, s14|->s13, s15|->s0, s15|->s2, s15|->s3, s15|->s5, s15|->s6, s15|->s7, s15|->s8, s15|->s10, s15|->s11, s15|->s12, s15|->s13, s16|->s0, s16|->s4, s16|->s5, s16|->s6, s16|->s8, s16|->s12, s16|->s13, s17|->s0, s17|->s4, s17|->s5, s17|->s13, s17|->s14, s18|->s1, s18|->s3, s18|->s5, s18|->s7, s18|->s8, s18|->s10, s18|->s11, s18|->s16, s18|->s17, s19|->s1, s19|->s5, s19|->s6, s19|->s7, s19|->s10, s19|->s12, s19|->s13, s19|->s15, s19|->s17, s19|->s18, s20|->s0, s20|->s3, s20|->s5, s20|->s7, s20|->s10, s20|->s11, s20|->s12, s20|->s13, s21|->s0, s21|->s1, s21|->s2, s21|->s5, s21|->s7, s21|->s9, s21|->s10, s21|->s11, s21|->s12, s21|->s13, s21|->s14, s21|->s15, s21|->s18, s21|->s19, s22|->s0, s22|->s1, s22|->s2, s22|->s3, s22|->s4, s22|->s8, s22|->s9, s22|->s10, s22|->s11, s22|->s14, s22|->s18, s22|->s19, s23|->s0, s23|->s1, s23|->s3, s23|->s6, s23|->s11, s23|->s17, s23|->s19, s23|->s20, s23|->s21, s23|->s22, s24|->s0, s24|->s2, s24|->s4, s24|->s6, s24|->s8, s24|->s9, s24|->s15, s24|->s16, s24|->s19, s24|->s22, s25|->s3, s25|->s4, s25|->s5, s25|->s6, s25|->s8, s25|->s9, s25|->s10, s25|->s12, s25|->s16, s25|->s18, s25|->s22, s25|->s23, s26|->s1, s26|->s2, s26|->s3, s26|->s4, s26|->s6, s26|->s7, s26|->s8, s26|->s11, s26|->s12, s26|->s13, s26|->s14, s26|->s15, s26|->s21, s26|->s22, s27|->s1, s27|->s5, s27|->s7, s27|->s8, s27|->s9, s27|->s12, s27|->s15, s27|->s19, s27|->s21, s27|->s22, s27|->s23, s27|->s25, s28|->s0, s28|->s1, s28|->s2, s28|->s3, s28|->s9, s28|->s13, s28|->s15, s28|->s16, s28|->s17, s28|->s18, s28|->s21, s28|->s22, s28|->s23, s28|->s25} &
    e_res={r2|->r0, r2|->r1, r3|->r0, r3|->r1, r4|->r0, r4|->r2, r4|->r3, r5|->r1, r5|->r2, r5|->r3, r6|->r1, r6|->r3, r7|->r0, r7|->r2, r7|->r3, r7|->r4, r7|->r5, r8|->r0, r8|->r1, r8|->r2, r8|->r3, r8|->r4, r9|->r0, r9|->r2, r9|->r5, r10|->r0, r10|->r2, r10|->r3, r10|->r5, r10|->r6, r10|->r7, r10|->r8, r10|->r9, r11|->r0, r11|->r2, r11|->r4, r11|->r5, r11|->r6, r11|->r7, r11|->r10, r12|->r6, r12|->r7, r13|->r0, r13|->r1, r13|->r2, r13|->r4, r13|->r6, r13|->r9, r13|->r11, r13|->r12, r14|->r0, r14|->r2, r14|->r4, r14|->r7, r14|->r8, r14|->r9, r14|->r13, r15|->r3, r15|->r5, r15|->r11, r15|->r13, r16|->r0, r16|->r1, r16|->r2, r16|->r5, r16|->r10, r16|->r12, r16|->r15, r17|->r1, r17|->r2, r17|->r3, r17|->r6, r17|->r9, r17|->r10, r17|->r12, r17|->r15, r18|->r0, r18|->r3, r18|->r4, r18|->r5, r18|->r6, r18|->r8, r18|->r9, r18|->r11, r18|->r13, r18|->r14, r18|->r15, r19|->r2, r19|->r3, r19|->r6, r19|->r7, r19|->r8, r19|->r13, r19|->r18, r20|->r0, r20|->r3, r20|->r5, r20|->r7, r20|->r11, r20|->r13, r20|->r15, r20|->r19, r21|->r1, r21|->r2, r21|->r3, r21|->r5, r21|->r7, r21|->r10, r21|->r14, r21|->r15, r21|->r16, r21|->r17, r21|->r18, r21|->r19, r22|->r5, r22|->r6, r22|->r7, r22|->r8, r22|->r9, r22|->r11, r22|->r15, r22|->r16, r22|->r17, r22|->r18, r22|->r20, r22|->r21, r23|->r0, r23|->r1, r23|->r3, r23|->r6, r23|->r7, r23|->r10, r23|->r12, r23|->r13, r23|->r14, r23|->r17, r23|->r18, r24|->r1, r24|->r3, r24|->r4, r24|->r5, r24|->r6, r24|->r7, r24|->r9, r24|->r10, r24|->r11, r24|->r12, r24|->r16, r24|->r17, r24|->r18, r24|->r20, r24|->r22, r25|->r0, r25|->r4, r25|->r6, r25|->r12, r25|->r15, r25|->r16, r25|->r20, r25|->r21, r25|->r22, r25|->r24} &
    rules={rule0|->(rec(su:s11,re:r23,mo:per,pr: 0,co:{c12,c7,c1})), rule1|->(rec(su:s0,re:r6,mo:per,pr: 3,co:{c9,c11,c5,c0,c6,c12,c7})), rule2|->(rec(su:s2,re:r17,mo:pro,pr: 2,co:{c2,c5,c4,c8,c7,c9,c1,c11}))}

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