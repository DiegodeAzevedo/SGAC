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
    e_sub={s1|->s0, s2|->s1, s3|->s0, s3|->s1, s4|->s0, s4|->s1, s4|->s3, s5|->s3, s6|->s1, s6|->s2, s7|->s1, s7|->s2, s7|->s4, s7|->s5, s8|->s2, s8|->s3, s8|->s5, s8|->s7, s9|->s0, s9|->s2, s9|->s3, s9|->s5, s10|->s0, s10|->s1, s10|->s2, s10|->s5, s10|->s6, s10|->s9, s11|->s1, s11|->s3, s11|->s5, s11|->s7, s11|->s8, s11|->s10, s12|->s0, s12|->s1, s12|->s3, s12|->s4, s12|->s5, s12|->s11, s13|->s3, s13|->s4, s13|->s9, s13|->s10, s14|->s3, s14|->s4, s14|->s6, s14|->s7, s14|->s9, s14|->s12, s15|->s0, s15|->s2, s15|->s3, s15|->s4, s15|->s5, s15|->s6, s15|->s7, s15|->s8, s15|->s11, s15|->s12, s15|->s14, s16|->s0, s16|->s1, s16|->s4, s16|->s5, s16|->s6, s16|->s8, s16|->s9, s16|->s10, s16|->s11, s16|->s13, s17|->s1, s17|->s2, s17|->s3, s17|->s5, s17|->s6, s17|->s7, s17|->s8, s17|->s9, s17|->s10, s17|->s11, s17|->s12, s17|->s15, s18|->s0, s18|->s1, s18|->s3, s18|->s5, s18|->s8, s18|->s9, s18|->s10, s18|->s12, s18|->s14, s18|->s15, s18|->s17, s19|->s0, s19|->s7, s19|->s9, s19|->s11, s19|->s14, s19|->s17, s20|->s2, s20|->s4, s20|->s6, s20|->s8, s20|->s9, s20|->s11, s20|->s12, s20|->s13, s20|->s14, s20|->s15, s20|->s16, s20|->s18, s20|->s19, s21|->s0, s21|->s1, s21|->s2, s21|->s13, s21|->s14, s21|->s15, s21|->s17, s21|->s18, s22|->s3, s22|->s7, s22|->s9, s22|->s10, s22|->s11, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s18, s23|->s2, s23|->s4, s23|->s7, s23|->s8, s23|->s9, s23|->s11, s23|->s19, s23|->s21, s23|->s22, s24|->s1, s24|->s5, s24|->s8, s24|->s10, s24|->s12, s24|->s13, s24|->s16, s24|->s18, s24|->s20, s25|->s1, s25|->s2, s25|->s5, s25|->s6, s25|->s7, s25|->s12, s25|->s14, s25|->s15, s25|->s16, s25|->s17, s25|->s18, s25|->s20, s25|->s21, s25|->s23, s26|->s2, s26|->s8, s26|->s10, s26|->s11, s26|->s12, s26|->s13, s26|->s16, s26|->s17, s26|->s18, s26|->s19, s26|->s20, s26|->s24, s26|->s25, s27|->s0, s27|->s1, s27|->s2, s27|->s4, s27|->s7, s27|->s8, s27|->s9, s27|->s12, s27|->s14, s27|->s15, s27|->s16, s27|->s17, s27|->s24, s28|->s1, s28|->s2, s28|->s4, s28|->s8, s28|->s11, s28|->s12, s28|->s16, s28|->s17, s28|->s18, s28|->s20, s28|->s21, s28|->s22, s28|->s23, s28|->s26, s29|->s1, s29|->s3, s29|->s5, s29|->s6, s29|->s7, s29|->s9, s29|->s12, s29|->s14, s29|->s15, s29|->s16, s29|->s21, s29|->s23, s29|->s24, s29|->s25, s29|->s27, s30|->s0, s30|->s1, s30|->s3, s30|->s4, s30|->s5, s30|->s6, s30|->s8, s30|->s9, s30|->s10, s30|->s11, s30|->s13, s30|->s14, s30|->s15, s30|->s18, s30|->s19, s30|->s20, s30|->s25, s30|->s26, s30|->s27, s30|->s29, s31|->s0, s31|->s3, s31|->s4, s31|->s7, s31|->s8, s31|->s9, s31|->s13, s31|->s14, s31|->s17, s31|->s18, s31|->s21, s31|->s23, s31|->s24, s31|->s29, s32|->s1, s32|->s3, s32|->s7, s32|->s9, s32|->s15, s32|->s16, s32|->s20, s32|->s22, s32|->s24, s32|->s25, s32|->s26, s32|->s27, s32|->s30, s33|->s0, s33|->s1, s33|->s2, s33|->s5, s33|->s6, s33|->s7, s33|->s9, s33|->s10, s33|->s11, s33|->s13, s33|->s15, s33|->s17, s33|->s19, s33|->s21, s33|->s22, s33|->s24, s33|->s29, s33|->s30, s33|->s31, s34|->s2, s34|->s5, s34|->s9, s34|->s10, s34|->s11, s34|->s14, s34|->s15, s34|->s18, s34|->s20, s34|->s21, s34|->s22, s34|->s28, s34|->s31, s34|->s33, s35|->s0, s35|->s2, s35|->s3, s35|->s4, s35|->s7, s35|->s8, s35|->s9, s35|->s10, s35|->s12, s35|->s13, s35|->s16, s35|->s17, s35|->s18, s35|->s19, s35|->s22, s35|->s25, s35|->s34, s36|->s2, s36|->s4, s36|->s5, s36|->s6, s36|->s8, s36|->s10, s36|->s11, s36|->s13, s36|->s20, s36|->s22, s36|->s23, s36|->s24, s37|->s0, s37|->s1, s37|->s3, s37|->s4, s37|->s5, s37|->s6, s37|->s7, s37|->s8, s37|->s9, s37|->s12, s37|->s13, s37|->s15, s37|->s16, s37|->s19, s37|->s21, s37|->s26, s37|->s27, s37|->s29, s37|->s32, s37|->s33, s37|->s34, s37|->s36, s38|->s4, s38|->s5, s38|->s7, s38|->s8, s38|->s11, s38|->s12, s38|->s14, s38|->s15, s38|->s17, s38|->s19, s38|->s20, s38|->s21, s38|->s23, s38|->s24, s38|->s28, s38|->s29, s38|->s30, s38|->s31, s38|->s32, s38|->s33, s38|->s34, s38|->s35, s38|->s36, s38|->s37, s39|->s2, s39|->s3, s39|->s5, s39|->s7, s39|->s9, s39|->s10, s39|->s18, s39|->s21, s39|->s22, s39|->s26, s39|->s27, s39|->s31, s39|->s34, s39|->s36, s39|->s38, s40|->s0, s40|->s1, s40|->s3, s40|->s7, s40|->s8, s40|->s10, s40|->s12, s40|->s15, s40|->s20, s40|->s22, s40|->s23, s40|->s25, s40|->s27, s40|->s31, s40|->s32, s40|->s36, s40|->s38, s40|->s39, s41|->s0, s41|->s4, s41|->s5, s41|->s7, s41|->s8, s41|->s11, s41|->s13, s41|->s14, s41|->s17, s41|->s19, s41|->s27, s41|->s28, s41|->s30, s41|->s31, s41|->s32, s41|->s33, s41|->s34, s41|->s37, s41|->s38, s41|->s39, s41|->s40, s42|->s0, s42|->s2, s42|->s3, s42|->s4, s42|->s6, s42|->s7, s42|->s8, s42|->s9, s42|->s10, s42|->s12, s42|->s13, s42|->s14, s42|->s16, s42|->s18, s42|->s19, s42|->s20, s42|->s23, s42|->s24, s42|->s25, s42|->s26, s42|->s27, s42|->s28, s42|->s29, s42|->s30, s42|->s31, s42|->s32, s42|->s34, s42|->s35, s42|->s41} &
    e_res={r1|->r0, r3|->r2, r4|->r0, r4|->r2, r5|->r0, r5|->r3, r5|->r4, r6|->r1, r6|->r4, r7|->r1, r7|->r2, r7|->r3, r7|->r4, r7|->r5, r8|->r1, r8|->r7, r9|->r0, r9|->r3, r9|->r5, r9|->r6, r9|->r8, r10|->r2, r10|->r6, r10|->r7, r10|->r8, r10|->r9, r11|->r0, r11|->r2, r11|->r3, r11|->r7, r11|->r8, r11|->r9, r12|->r0, r12|->r1, r12|->r2, r12|->r3, r12|->r5, r12|->r9, r12|->r10, r12|->r11, r13|->r0, r13|->r3, r13|->r4, r13|->r6, r13|->r10, r13|->r11, r13|->r12, r14|->r0, r14|->r4, r14|->r7, r14|->r9, r14|->r12, r14|->r13, r15|->r0, r15|->r2, r15|->r4, r15|->r6, r15|->r7, r15|->r9, r15|->r10, r15|->r11, r15|->r14, r16|->r0, r16|->r1, r16|->r2, r16|->r6, r16|->r8, r16|->r9, r16|->r13, r16|->r14, r17|->r0, r17|->r1, r17|->r3, r17|->r7, r17|->r11, r17|->r12, r17|->r13, r17|->r14, r17|->r16, r18|->r1, r18|->r2, r18|->r4, r18|->r8, r18|->r9, r18|->r10, r18|->r11, r18|->r12, r18|->r14, r18|->r16, r18|->r17, r19|->r0, r19|->r1, r19|->r2, r19|->r3, r19|->r6, r19|->r9, r19|->r10, r19|->r11, r19|->r12, r19|->r13, r19|->r16, r20|->r0, r20|->r1, r20|->r3, r20|->r5, r20|->r10, r20|->r11, r20|->r12, r20|->r15, r20|->r16, r20|->r18, r20|->r19, r21|->r0, r21|->r1, r21|->r3, r21|->r6, r21|->r7, r21|->r9, r21|->r12, r21|->r14, r22|->r1, r22|->r2, r22|->r3, r22|->r4, r22|->r5, r22|->r9, r22|->r10, r22|->r11, r22|->r13, r22|->r17, r22|->r18, r22|->r19, r22|->r20, r22|->r21, r23|->r1, r23|->r3, r23|->r6, r23|->r8, r23|->r9, r23|->r12, r23|->r15, r23|->r17, r23|->r18, r23|->r21, r23|->r22, r24|->r2, r24|->r3, r24|->r9, r24|->r11, r24|->r13, r24|->r15, r24|->r17, r24|->r19, r24|->r22, r25|->r3, r25|->r5, r25|->r13, r25|->r17, r25|->r20, r25|->r21, r26|->r0, r26|->r1, r26|->r3, r26|->r4, r26|->r5, r26|->r6, r26|->r7, r26|->r8, r26|->r11, r26|->r12, r26|->r13, r26|->r14, r26|->r16, r26|->r18, r26|->r24, r26|->r25, r27|->r1, r27|->r3, r27|->r5, r27|->r8, r27|->r9, r27|->r13, r27|->r15, r27|->r17, r27|->r20, r27|->r22, r27|->r23, r27|->r24, r27|->r25, r28|->r0, r28|->r1, r28|->r2, r28|->r3, r28|->r5, r28|->r7, r28|->r8, r28|->r10, r28|->r12, r28|->r13, r28|->r15, r28|->r18, r28|->r19, r28|->r20, r28|->r22, r28|->r25, r29|->r0, r29|->r1, r29|->r2, r29|->r4, r29|->r5, r29|->r6, r29|->r8, r29|->r10, r29|->r13, r29|->r16, r29|->r17, r29|->r18, r29|->r20, r29|->r23, r29|->r25, r29|->r26, r29|->r27, r30|->r1, r30|->r4, r30|->r5, r30|->r6, r30|->r7, r30|->r9, r30|->r10, r30|->r12, r30|->r17, r30|->r18, r30|->r22, r30|->r26, r30|->r28, r30|->r29, r31|->r1, r31|->r3, r31|->r4, r31|->r5, r31|->r6, r31|->r13, r31|->r14, r31|->r16, r31|->r17, r31|->r18, r31|->r19, r31|->r20, r31|->r22, r31|->r25, r31|->r29, r32|->r0, r32|->r1, r32|->r3, r32|->r5, r32|->r6, r32|->r8, r32|->r9, r32|->r13, r32|->r15, r32|->r16, r32|->r17, r32|->r18, r32|->r19, r32|->r22, r32|->r24, r32|->r25, r32|->r27, r32|->r29, r32|->r30, r32|->r31, r33|->r0, r33|->r2, r33|->r3, r33|->r4, r33|->r8, r33|->r9, r33|->r16, r33|->r17, r33|->r21, r33|->r24, r33|->r26, r33|->r29, r33|->r30, r33|->r31, r34|->r4, r34|->r7, r34|->r8, r34|->r9, r34|->r11, r34|->r17, r34|->r18, r34|->r20, r34|->r21, r34|->r26, r34|->r27, r34|->r28, r34|->r29, r34|->r30, r34|->r31, r34|->r32, r34|->r33, r35|->r1, r35|->r4, r35|->r5, r35|->r6, r35|->r7, r35|->r8, r35|->r9, r35|->r10, r35|->r14, r35|->r15, r35|->r17, r35|->r20, r35|->r22, r35|->r25, r35|->r26, r35|->r27, r35|->r29, r35|->r30, r35|->r32, r35|->r34, r36|->r0, r36|->r5, r36|->r7, r36|->r17, r36|->r19, r36|->r21, r36|->r22, r36|->r24, r36|->r25, r36|->r26, r36|->r29, r36|->r31, r36|->r32, r36|->r33, r37|->r1, r37|->r2, r37|->r6, r37|->r7, r37|->r8, r37|->r11, r37|->r12, r37|->r13, r37|->r15, r37|->r17, r37|->r26, r37|->r27, r37|->r28, r37|->r29, r37|->r31, r37|->r32, r37|->r33, r37|->r35, r37|->r36, r38|->r0, r38|->r4, r38|->r5, r38|->r7, r38|->r9, r38|->r10, r38|->r11, r38|->r12, r38|->r13, r38|->r15, r38|->r16, r38|->r17, r38|->r21, r38|->r22, r38|->r23, r38|->r24, r38|->r25, r38|->r29, r38|->r31, r38|->r33, r38|->r34, r38|->r35, r38|->r37, r39|->r2, r39|->r7, r39|->r9, r39|->r10, r39|->r11, r39|->r12, r39|->r14, r39|->r16, r39|->r17, r39|->r19, r39|->r23, r39|->r24, r39|->r25, r39|->r26, r39|->r27, r39|->r28, r39|->r30, r39|->r31, r39|->r32, r39|->r34, r39|->r35, r39|->r36, r39|->r38, r40|->r1, r40|->r3, r40|->r5, r40|->r6, r40|->r7, r40|->r16, r40|->r17, r40|->r20, r40|->r22, r40|->r23, r40|->r25, r40|->r26, r40|->r27, r40|->r28, r40|->r29, r40|->r30, r40|->r32, r40|->r33, r40|->r34, r41|->r0, r41|->r1, r41|->r3, r41|->r5, r41|->r6, r41|->r7, r41|->r8, r41|->r9, r41|->r12, r41|->r14, r41|->r16, r41|->r22, r41|->r26, r41|->r32, r41|->r33, r41|->r34, r41|->r37, r41|->r40} &
    rules={rule0|->(rec(su:s27,re:r25,mo:per,pr: 2,co:{c7,c5,c9,c8,c2})), rule1|->(rec(su:s9,re:r29,mo:per,pr: 1,co:{c1,c4,c2,c5,c3,c6,c7,c9})), rule2|->(rec(su:s0,re:r1,mo:per,pr: 2,co:{c9,c4})), rule3|->(rec(su:s8,re:r5,mo:pro,pr: 0,co:{c5,c9,c7,c1,c6})), rule4|->(rec(su:s40,re:r35,mo:pro,pr: 0,co:{c8,c2,c3,c5})), rule5|->(rec(su:s1,re:r5,mo:pro,pr: 3,co:{c7,c3,c4,c1,c2,c6,c0})), rule6|->(rec(su:s29,re:r25,mo:pro,pr: 2,co:{c9,c0})), rule7|->(rec(su:s14,re:r29,mo:per,pr: 1,co:{c4,c1,c0,c9,c8,c3,c2,c5})), rule8|->(rec(su:s1,re:r6,mo:per,pr: 1,co:{c8,c7,c6,c3,c4})), rule9|->(rec(su:s5,re:r15,mo:pro,pr: 3,co:{c1,c6,c5,c4,c2,c0,c3})), rule10|->(rec(su:s22,re:r7,mo:pro,pr: 3,co:{c9,c7})), rule11|->(rec(su:s34,re:r12,mo:per,pr: 3,co:{c7})), rule12|->(rec(su:s37,re:r8,mo:per,pr: 4,co:{c4,c0,c5}))}

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