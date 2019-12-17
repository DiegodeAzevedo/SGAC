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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41};
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
    e_sub={s2|->s1, s3|->s0, s3|->s1, s4|->s2, s4|->s3, s5|->s0, s5|->s1, s5|->s4, s6|->s0, s6|->s2, s6|->s3, s6|->s4, s7|->s0, s7|->s1, s7|->s4, s7|->s5, s8|->s2, s8|->s3, s8|->s4, s8|->s6, s8|->s7, s9|->s0, s9|->s1, s9|->s3, s9|->s6, s9|->s7, s9|->s8, s10|->s0, s10|->s1, s10|->s2, s10|->s4, s10|->s7, s11|->s0, s11|->s1, s11|->s5, s11|->s8, s12|->s1, s12|->s2, s12|->s7, s12|->s8, s12|->s10, s12|->s11, s13|->s1, s13|->s4, s13|->s7, s13|->s8, s13|->s10, s14|->s1, s14|->s3, s14|->s4, s14|->s5, s14|->s8, s14|->s9, s14|->s12, s15|->s0, s15|->s1, s15|->s6, s15|->s10, s15|->s12, s15|->s13, s16|->s0, s16|->s1, s16|->s3, s16|->s4, s16|->s8, s16|->s9, s16|->s13, s16|->s14, s17|->s3, s17|->s6, s17|->s13, s18|->s0, s18|->s6, s18|->s7, s18|->s8, s18|->s9, s18|->s10, s18|->s13, s18|->s15, s18|->s17, s19|->s0, s19|->s1, s19|->s2, s19|->s3, s19|->s4, s19|->s5, s19|->s11, s19|->s13, s19|->s18, s20|->s3, s20|->s6, s20|->s7, s20|->s9, s20|->s11, s20|->s13, s20|->s16, s21|->s1, s21|->s2, s21|->s5, s21|->s6, s21|->s8, s21|->s9, s21|->s11, s21|->s12, s21|->s14, s21|->s15, s21|->s16, s21|->s19, s22|->s0, s22|->s1, s22|->s2, s22|->s4, s22|->s6, s22|->s7, s22|->s8, s22|->s11, s22|->s13, s22|->s18, s22|->s19, s22|->s20, s23|->s0, s23|->s3, s23|->s5, s23|->s7, s23|->s10, s23|->s11, s23|->s16, s23|->s17, s23|->s19, s23|->s20, s23|->s21, s24|->s1, s24|->s2, s24|->s3, s24|->s5, s24|->s10, s24|->s11, s24|->s13, s24|->s14, s24|->s19, s24|->s23, s25|->s0, s25|->s2, s25|->s3, s25|->s5, s25|->s6, s25|->s7, s25|->s8, s25|->s9, s25|->s11, s25|->s14, s25|->s15, s25|->s16, s25|->s17, s25|->s19, s25|->s20, s25|->s21, s25|->s23, s26|->s2, s26|->s4, s26|->s5, s26|->s9, s26|->s13, s26|->s19, s26|->s20, s26|->s25, s27|->s0, s27|->s1, s27|->s5, s27|->s6, s27|->s14, s27|->s16, s27|->s17, s27|->s20, s27|->s21, s27|->s22, s27|->s24, s28|->s2, s28|->s3, s28|->s5, s28|->s6, s28|->s7, s28|->s10, s28|->s11, s28|->s13, s28|->s14, s28|->s15, s28|->s17, s28|->s20, s28|->s26, s29|->s1, s29|->s2, s29|->s3, s29|->s5, s29|->s6, s29|->s7, s29|->s9, s29|->s11, s29|->s12, s29|->s13, s29|->s14, s29|->s16, s29|->s18, s29|->s19, s29|->s21, s29|->s23, s29|->s24, s29|->s25, s29|->s26, s29|->s28, s30|->s0, s30|->s1, s30|->s2, s30|->s4, s30|->s6, s30|->s12, s30|->s14, s30|->s16, s30|->s22, s30|->s23, s30|->s24, s31|->s2, s31|->s3, s31|->s6, s31|->s8, s31|->s11, s31|->s17, s31|->s19, s31|->s20, s31|->s21, s31|->s24, s31|->s28, s31|->s29, s32|->s0, s32|->s1, s32|->s2, s32|->s4, s32|->s5, s32|->s9, s32|->s14, s32|->s16, s32|->s17, s32|->s18, s32|->s19, s32|->s21, s32|->s24, s32|->s25, s32|->s27, s32|->s28, s32|->s30, s33|->s0, s33|->s1, s33|->s2, s33|->s3, s33|->s5, s33|->s6, s33|->s8, s33|->s10, s33|->s13, s33|->s14, s33|->s15, s33|->s16, s33|->s19, s33|->s21, s33|->s23, s33|->s25, s33|->s26, s33|->s27, s33|->s28, s33|->s29, s33|->s30, s33|->s32, s34|->s3, s34|->s4, s34|->s5, s34|->s6, s34|->s8, s34|->s9, s34|->s10, s34|->s11, s34|->s14, s34|->s16, s34|->s19, s34|->s20, s34|->s21, s34|->s24, s34|->s25, s34|->s26, s34|->s27, s34|->s30, s34|->s32, s34|->s33, s35|->s0, s35|->s1, s35|->s3, s35|->s4, s35|->s6, s35|->s7, s35|->s8, s35|->s11, s35|->s13, s35|->s14, s35|->s15, s35|->s18, s35|->s22, s35|->s24, s35|->s26, s35|->s27, s35|->s28, s35|->s29, s35|->s31, s35|->s33, s35|->s34, s36|->s1, s36|->s3, s36|->s4, s36|->s6, s36|->s7, s36|->s10, s36|->s12, s36|->s18, s36|->s19, s36|->s22, s36|->s25, s36|->s28, s36|->s29, s36|->s30, s36|->s35, s37|->s0, s37|->s2, s37|->s3, s37|->s5, s37|->s9, s37|->s11, s37|->s12, s37|->s13, s37|->s17, s37|->s22, s37|->s24, s37|->s25, s37|->s26, s37|->s27, s37|->s28, s37|->s31, s37|->s32, s37|->s36, s38|->s0, s38|->s1, s38|->s2, s38|->s3, s38|->s5, s38|->s6, s38|->s7, s38|->s8, s38|->s9, s38|->s11, s38|->s15, s38|->s16, s38|->s17, s38|->s18, s38|->s19, s38|->s20, s38|->s21, s38|->s22, s38|->s24, s38|->s25, s38|->s26, s38|->s27, s38|->s28, s38|->s30, s38|->s33, s38|->s34, s38|->s35, s38|->s36, s39|->s0, s39|->s6, s39|->s8, s39|->s10, s39|->s11, s39|->s14, s39|->s19, s39|->s23, s39|->s25, s39|->s27, s39|->s28, s39|->s30, s39|->s31, s39|->s32, s39|->s33, s39|->s34, s39|->s36, s40|->s0, s40|->s1, s40|->s2, s40|->s6, s40|->s8, s40|->s9, s40|->s10, s40|->s11, s40|->s12, s40|->s16, s40|->s18, s40|->s19, s40|->s21, s40|->s22, s40|->s23, s40|->s24, s40|->s26, s40|->s29, s40|->s34, s40|->s36, s40|->s37, s40|->s39, s41|->s0, s41|->s1, s41|->s2, s41|->s4, s41|->s5, s41|->s6, s41|->s9, s41|->s10, s41|->s12, s41|->s13, s41|->s15, s41|->s16, s41|->s20, s41|->s22, s41|->s27, s41|->s28, s41|->s29, s41|->s30, s41|->s31, s41|->s34, s41|->s36, s41|->s40, s42|->s1, s42|->s3, s42|->s4, s42|->s7, s42|->s9, s42|->s11, s42|->s16, s42|->s17, s42|->s18, s42|->s19, s42|->s20, s42|->s25, s42|->s26, s42|->s27, s42|->s29, s42|->s30, s42|->s33, s42|->s35, s42|->s36, s42|->s37, s42|->s40, s42|->s41} &
    e_res={r1|->r0, r2|->r0, r3|->r2, r4|->r0, r4|->r1, r4|->r2, r4|->r3, r5|->r0, r5|->r1, r5|->r3, r5|->r4, r6|->r0, r6|->r1, r6|->r2, r6|->r3, r6|->r5, r7|->r1, r7|->r2, r7|->r4, r7|->r5, r8|->r6, r8|->r7, r9|->r0, r9|->r1, r9|->r4, r9|->r5, r9|->r6, r9|->r8, r10|->r1, r10|->r2, r10|->r4, r10|->r6, r11|->r0, r11|->r5, r12|->r2, r12|->r8, r12|->r11, r13|->r0, r13|->r1, r13|->r2, r13|->r5, r13|->r8, r13|->r9, r13|->r11, r13|->r12, r14|->r4, r14|->r5, r14|->r9, r14|->r11, r15|->r1, r15|->r4, r15|->r5, r15|->r7, r15|->r8, r15|->r9, r15|->r10, r15|->r11, r15|->r12, r15|->r13, r16|->r2, r16|->r3, r16|->r5, r16|->r6, r16|->r8, r16|->r9, r16|->r11, r16|->r12, r16|->r14, r16|->r15, r17|->r0, r17|->r2, r17|->r3, r17|->r4, r17|->r5, r17|->r7, r17|->r8, r17|->r9, r17|->r11, r17|->r13, r17|->r14, r17|->r16, r18|->r0, r18|->r2, r18|->r3, r18|->r5, r18|->r6, r18|->r7, r18|->r10, r18|->r11, r18|->r13, r19|->r0, r19|->r5, r19|->r10, r19|->r13, r19|->r16, r20|->r1, r20|->r2, r20|->r3, r20|->r6, r20|->r7, r20|->r8, r20|->r10, r20|->r14, r20|->r16, r20|->r17, r20|->r19, r21|->r0, r21|->r1, r21|->r2, r21|->r5, r21|->r6, r21|->r7, r21|->r9, r21|->r10, r21|->r12, r21|->r13, r21|->r15, r21|->r16, r21|->r17, r21|->r19, r22|->r1, r22|->r2, r22|->r4, r22|->r8, r22|->r9, r22|->r11, r22|->r12, r22|->r14, r22|->r18, r22|->r20, r23|->r0, r23|->r1, r23|->r3, r23|->r4, r23|->r6, r23|->r9, r23|->r12, r23|->r19, r23|->r21, r24|->r3, r24|->r6, r24|->r7, r24|->r8, r24|->r9, r24|->r12, r24|->r13, r24|->r14, r24|->r15, r24|->r19, r24|->r22, r25|->r1, r25|->r2, r25|->r6, r25|->r8, r25|->r9, r25|->r10, r25|->r13, r25|->r15, r25|->r18, r25|->r20, r25|->r21, r25|->r24, r26|->r1, r26|->r6, r26|->r8, r26|->r12, r26|->r13, r26|->r15, r26|->r20, r26|->r21, r26|->r24, r26|->r25, r27|->r0, r27|->r1, r27|->r2, r27|->r4, r27|->r7, r27|->r8, r27|->r15, r27|->r16, r27|->r17, r27|->r18, r27|->r20, r27|->r21, r27|->r23, r27|->r24, r27|->r25, r27|->r26, r28|->r0, r28|->r3, r28|->r5, r28|->r6, r28|->r8, r28|->r9, r28|->r12, r28|->r15, r28|->r16, r28|->r18, r28|->r19, r28|->r20, r28|->r22, r28|->r24, r29|->r2, r29|->r3, r29|->r4, r29|->r5, r29|->r6, r29|->r7, r29|->r10, r29|->r11, r29|->r12, r29|->r13, r29|->r17, r29|->r20, r29|->r21, r29|->r22, r29|->r25, r29|->r28, r30|->r2, r30|->r4, r30|->r8, r30|->r9, r30|->r10, r30|->r11, r30|->r14, r30|->r16, r30|->r19, r30|->r20, r30|->r21, r30|->r26, r30|->r29, r31|->r2, r31|->r3, r31|->r4, r31|->r6, r31|->r10, r31|->r17, r31|->r20, r31|->r23, r31|->r24, r31|->r26, r31|->r28, r32|->r0, r32|->r1, r32|->r2, r32|->r3, r32|->r4, r32|->r9, r32|->r10, r32|->r11, r32|->r12, r32|->r15, r32|->r19, r32|->r21, r32|->r22, r32|->r24, r32|->r26, r32|->r27, r32|->r29, r32|->r30, r33|->r2, r33|->r3, r33|->r4, r33|->r5, r33|->r7, r33|->r9, r33|->r11, r33|->r12, r33|->r13, r33|->r14, r33|->r15, r33|->r17, r33|->r18, r33|->r22, r33|->r26, r33|->r27, r33|->r28, r33|->r30, r33|->r32, r34|->r0, r34|->r2, r34|->r3, r34|->r7, r34|->r8, r34|->r9, r34|->r10, r34|->r12, r34|->r16, r34|->r19, r34|->r20, r34|->r22, r34|->r23, r34|->r24, r34|->r28, r34|->r29, r34|->r30, r35|->r0, r35|->r3, r35|->r5, r35|->r6, r35|->r7, r35|->r9, r35|->r10, r35|->r19, r35|->r21, r35|->r22, r35|->r24, r35|->r26, r35|->r27, r35|->r28, r35|->r29, r35|->r30, r35|->r32, r35|->r33, r35|->r34, r36|->r2, r36|->r3, r36|->r5, r36|->r6, r36|->r7, r36|->r11, r36|->r12, r36|->r14, r36|->r16, r36|->r17, r36|->r18, r36|->r19, r36|->r20, r36|->r21, r36|->r22, r36|->r23, r36|->r24, r36|->r25, r36|->r29, r36|->r30, r36|->r32, r36|->r34, r37|->r0, r37|->r1, r37|->r2, r37|->r3, r37|->r4, r37|->r9, r37|->r11, r37|->r13, r37|->r14, r37|->r15, r37|->r19, r37|->r20, r37|->r22, r37|->r23, r37|->r24, r37|->r27, r37|->r28, r37|->r29, r37|->r31, r37|->r34, r38|->r2, r38|->r4, r38|->r6, r38|->r8, r38|->r9, r38|->r10, r38|->r12, r38|->r13, r38|->r14, r38|->r15, r38|->r16, r38|->r20, r38|->r22, r38|->r26, r38|->r29, r38|->r32, r38|->r36, r39|->r0, r39|->r1, r39|->r2, r39|->r4, r39|->r6, r39|->r8, r39|->r9, r39|->r11, r39|->r12, r39|->r14, r39|->r15, r39|->r16, r39|->r17, r39|->r24, r39|->r26, r39|->r27, r39|->r28, r39|->r30, r39|->r34, r39|->r38, r40|->r2, r40|->r4, r40|->r5, r40|->r6, r40|->r8, r40|->r10, r40|->r13, r40|->r15, r40|->r22, r40|->r23, r40|->r24, r40|->r26, r40|->r28, r40|->r29, r40|->r32, r40|->r36, r40|->r38, r41|->r1, r41|->r5, r41|->r7, r41|->r8, r41|->r11, r41|->r12, r41|->r15, r41|->r16, r41|->r18, r41|->r19, r41|->r22, r41|->r27, r41|->r28, r41|->r33, r41|->r34, r41|->r35, r41|->r38, r41|->r39, r41|->r40} &
    rules={rule0|->(rec(su:s29,re:r4,mo:per,pr: 1,co:{c9,c2,c5,c4})), rule1|->(rec(su:s2,re:r4,mo:per,pr: 0,co:{c0,c8,c6,c3})), rule2|->(rec(su:s29,re:r39,mo:per,pr: 4,co:{c0,c1,c3,c5})), rule3|->(rec(su:s18,re:r38,mo:per,pr: 1,co:{c6,c8,c0})), rule4|->(rec(su:s38,re:r15,mo:per,pr: 2,co:{c8,c0,c4,c1,c7})), rule5|->(rec(su:s15,re:r0,mo:per,pr: 0,co:{c3,c4,c6,c8,c1,c7})), rule6|->(rec(su:s42,re:r34,mo:per,pr: 0,co:{c0})), rule7|->(rec(su:s37,re:r37,mo:per,pr: 2,co:{c8,c4,c6,c2,c7,c5,c9,c1})), rule8|->(rec(su:s18,re:r37,mo:per,pr: 1,co:{c6,c1,c4,c3,c2})), rule9|->(rec(su:s35,re:r35,mo:pro,pr: 2,co:{c9,c3,c7,c5,c1,c8})), rule10|->(rec(su:s27,re:r18,mo:per,pr: 2,co:{c7,c1,c5,c6})), rule11|->(rec(su:s6,re:r36,mo:pro,pr: 3,co:{c8,c4})), rule12|->(rec(su:s39,re:r14,mo:pro,pr: 1,co:{c0,c9,c7,c4,c1}))}

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