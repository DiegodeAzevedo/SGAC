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
    e_sub={s2|->s1, s3|->s0, s3|->s2, s4|->s2, s5|->s0, s5|->s1, s5|->s2, s6|->s3, s6|->s4, s7|->s0, s7|->s1, s7|->s2, s7|->s3, s7|->s4, s8|->s1, s8|->s2, s8|->s6, s9|->s0, s9|->s1, s9|->s2, s9|->s3, s10|->s3, s10|->s4, s10|->s5, s10|->s7, s10|->s8, s11|->s2, s11|->s3, s11|->s4, s11|->s5, s11|->s6, s11|->s7, s11|->s8, s12|->s2, s12|->s3, s12|->s8, s12|->s11, s13|->s1, s13|->s3, s13|->s6, s13|->s8, s13|->s9, s13|->s12, s14|->s0, s14|->s1, s14|->s3, s14|->s4, s14|->s5, s14|->s8, s14|->s10, s15|->s1, s15|->s3, s15|->s4, s15|->s5, s15|->s6, s15|->s8, s15|->s13, s15|->s14, s16|->s3, s16|->s4, s16|->s5, s16|->s7, s16|->s8, s16|->s10, s16|->s11, s16|->s12, s17|->s1, s17|->s2, s17|->s3, s17|->s6, s17|->s8, s17|->s13, s17|->s14, s17|->s16, s18|->s1, s18|->s2, s18|->s3, s18|->s4, s18|->s5, s18|->s8, s18|->s9, s18|->s11, s18|->s12, s18|->s15, s18|->s17, s19|->s2, s19|->s3, s19|->s4, s19|->s5, s19|->s6, s19|->s8, s19|->s9, s19|->s11, s19|->s13, s19|->s15, s19|->s16, s19|->s17, s19|->s18, s20|->s0, s20|->s1, s20|->s2, s20|->s3, s20|->s9, s20|->s11, s20|->s12, s20|->s14, s21|->s0, s21|->s3, s21|->s4, s21|->s5, s21|->s6, s21|->s9, s21|->s11, s21|->s12, s21|->s14, s21|->s19, s21|->s20, s22|->s2, s22|->s7, s22|->s8, s22|->s9, s22|->s11, s22|->s13, s22|->s14, s22|->s15, s22|->s16, s22|->s17, s22|->s18, s22|->s19, s22|->s21, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s5, s23|->s10, s23|->s12, s23|->s13, s23|->s15, s23|->s16, s23|->s17, s23|->s18, s23|->s19, s23|->s20, s23|->s22, s24|->s0, s24|->s1, s24|->s5, s24|->s6, s24|->s11, s24|->s12, s24|->s14, s24|->s17, s24|->s18, s24|->s21, s24|->s23, s25|->s2, s25|->s3, s25|->s7, s25|->s9, s25|->s11, s25|->s13, s25|->s14, s25|->s15, s25|->s17, s25|->s18, s25|->s19, s25|->s20, s25|->s23, s25|->s24, s26|->s2, s26|->s4, s26|->s5, s26|->s6, s26|->s13, s26|->s14, s26|->s16, s26|->s17, s26|->s20, s26|->s23, s26|->s24, s27|->s2, s27|->s5, s27|->s7, s27|->s9, s27|->s10, s27|->s11, s27|->s12, s27|->s14, s27|->s15, s27|->s17, s27|->s20, s27|->s21, s27|->s25, s27|->s26, s28|->s0, s28|->s3, s28|->s4, s28|->s6, s28|->s7, s28|->s11, s28|->s13, s28|->s14, s28|->s15, s28|->s22, s28|->s23, s29|->s0, s29|->s3, s29|->s4, s29|->s5, s29|->s7, s29|->s9, s29|->s12, s29|->s17, s29|->s20, s29|->s22, s29|->s23, s29|->s24, s29|->s25, s29|->s28, s30|->s0, s30|->s1, s30|->s2, s30|->s4, s30|->s5, s30|->s6, s30|->s10, s30|->s11, s30|->s14, s30|->s17, s30|->s19, s30|->s23, s30|->s24, s30|->s25, s30|->s26, s30|->s27, s30|->s29, s31|->s3, s31|->s4, s31|->s5, s31|->s6, s31|->s9, s31|->s10, s31|->s11, s31|->s12, s31|->s16, s31|->s17, s31|->s21, s31|->s22, s31|->s24, s31|->s25, s31|->s26, s31|->s27, s31|->s28, s31|->s29, s31|->s30, s32|->s0, s32|->s2, s32|->s4, s32|->s5, s32|->s7, s32|->s9, s32|->s10, s32|->s11, s32|->s12, s32|->s13, s32|->s14, s32|->s19, s32|->s22, s32|->s24, s32|->s25, s32|->s28, s32|->s30, s33|->s3, s33|->s4, s33|->s6, s33|->s8, s33|->s11, s33|->s17, s33|->s18, s33|->s21, s33|->s26, s33|->s28, s33|->s30, s33|->s31, s33|->s32, s34|->s1, s34|->s6, s34|->s7, s34|->s8, s34|->s9, s34|->s11, s34|->s12, s34|->s13, s34|->s14, s34|->s15, s34|->s16, s34|->s17, s34|->s18, s34|->s19, s34|->s23, s34|->s25, s34|->s27, s34|->s30, s34|->s33, s35|->s1, s35|->s5, s35|->s6, s35|->s7, s35|->s9, s35|->s10, s35|->s12, s35|->s13, s35|->s15, s35|->s17, s35|->s18, s35|->s19, s35|->s20, s35|->s22, s35|->s25, s35|->s27, s35|->s28, s35|->s32, s35|->s34, s36|->s1, s36|->s4, s36|->s5, s36|->s6, s36|->s7, s36|->s8, s36|->s10, s36|->s12, s36|->s14, s36|->s16, s36|->s18, s36|->s19, s36|->s22, s36|->s23, s36|->s25, s36|->s26, s36|->s28, s36|->s30, s36|->s31, s36|->s35, s37|->s1, s37|->s3, s37|->s5, s37|->s6, s37|->s9, s37|->s12, s37|->s13, s37|->s14, s37|->s16, s37|->s20, s37|->s21, s37|->s24, s37|->s25, s37|->s26, s37|->s28, s37|->s29, s37|->s33, s37|->s34, s37|->s35, s37|->s36, s38|->s3, s38|->s4, s38|->s5, s38|->s7, s38|->s9, s38|->s11, s38|->s12, s38|->s13, s38|->s15, s38|->s19, s38|->s22, s38|->s25, s38|->s26, s38|->s27, s38|->s28, s38|->s29, s38|->s30, s38|->s31, s38|->s33, s38|->s34, s38|->s36, s39|->s0, s39|->s1, s39|->s2, s39|->s3, s39|->s4, s39|->s5, s39|->s6, s39|->s10, s39|->s12, s39|->s13, s39|->s19, s39|->s20, s39|->s21, s39|->s24, s39|->s26, s39|->s28, s39|->s29, s39|->s30, s39|->s32, s39|->s33, s39|->s34, s39|->s35, s39|->s38, s40|->s4, s40|->s6, s40|->s7, s40|->s12, s40|->s14, s40|->s15, s40|->s16, s40|->s18, s40|->s21, s40|->s23, s40|->s27, s40|->s28, s40|->s31, s40|->s33, s40|->s35, s40|->s36, s40|->s37, s40|->s38, s41|->s1, s41|->s3, s41|->s5, s41|->s7, s41|->s8, s41|->s9, s41|->s10, s41|->s11, s41|->s14, s41|->s15, s41|->s16, s41|->s17, s41|->s18, s41|->s25, s41|->s26, s41|->s27, s41|->s29, s41|->s30, s41|->s31, s41|->s33, s41|->s35, s41|->s36, s41|->s38, s41|->s40, s42|->s0, s42|->s1, s42|->s2, s42|->s4, s42|->s6, s42|->s7, s42|->s9, s42|->s14, s42|->s18, s42|->s19, s42|->s20, s42|->s21, s42|->s22, s42|->s24, s42|->s26, s42|->s27, s42|->s29, s42|->s30, s42|->s31, s42|->s32, s42|->s34} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r3|->r1, r3|->r2, r4|->r1, r4|->r2, r5|->r0, r5|->r1, r5|->r2, r5|->r3, r5|->r4, r6|->r0, r6|->r2, r6|->r3, r7|->r4, r7|->r5, r8|->r2, r8|->r3, r8|->r4, r8|->r7, r9|->r0, r9|->r1, r9|->r2, r9|->r4, r9|->r6, r10|->r0, r10|->r3, r10|->r8, r10|->r9, r11|->r0, r11|->r2, r11|->r4, r11|->r5, r11|->r6, r11|->r7, r11|->r8, r11|->r9, r12|->r0, r12|->r1, r12|->r3, r12|->r5, r12|->r7, r12|->r9, r12|->r10, r13|->r2, r13|->r4, r13|->r6, r13|->r9, r14|->r0, r14|->r1, r14|->r2, r14|->r4, r14|->r7, r14|->r8, r14|->r13, r15|->r0, r15|->r4, r15|->r8, r15|->r10, r15|->r11, r15|->r13, r16|->r1, r16|->r3, r16|->r6, r16|->r8, r16|->r9, r16|->r10, r16|->r12, r16|->r14, r17|->r3, r17|->r5, r17|->r7, r17|->r10, r17|->r13, r17|->r15, r18|->r0, r18|->r2, r18|->r6, r18|->r9, r18|->r15, r18|->r16, r18|->r17, r19|->r0, r19|->r2, r19|->r3, r19|->r7, r19|->r8, r19|->r9, r19|->r10, r19|->r12, r19|->r13, r19|->r14, r19|->r15, r19|->r16, r19|->r17, r20|->r1, r20|->r4, r20|->r7, r20|->r8, r20|->r9, r20|->r10, r20|->r11, r20|->r14, r20|->r15, r20|->r17, r21|->r0, r21|->r2, r21|->r5, r21|->r6, r21|->r10, r21|->r11, r21|->r13, r21|->r14, r21|->r16, r21|->r17, r21|->r18, r21|->r20, r22|->r0, r22|->r1, r22|->r3, r22|->r4, r22|->r5, r22|->r7, r22|->r8, r22|->r11, r22|->r12, r22|->r13, r22|->r18, r22|->r20, r22|->r21, r23|->r3, r23|->r5, r23|->r6, r23|->r12, r23|->r13, r23|->r14, r23|->r15, r23|->r17, r23|->r18, r23|->r19, r23|->r20, r24|->r3, r24|->r4, r24|->r5, r24|->r8, r24|->r9, r24|->r10, r24|->r11, r24|->r15, r24|->r16, r24|->r18, r24|->r19, r24|->r21, r24|->r23, r25|->r0, r25|->r1, r25|->r2, r25|->r3, r25|->r4, r25|->r7, r25|->r10, r25|->r12, r25|->r13, r25|->r16, r25|->r17, r25|->r18, r25|->r20, r26|->r2, r26|->r3, r26|->r4, r26|->r5, r26|->r7, r26|->r13, r26|->r15, r26|->r19, r26|->r23, r26|->r24, r27|->r0, r27|->r1, r27|->r2, r27|->r3, r27|->r4, r27|->r5, r27|->r6, r27|->r7, r27|->r12, r27|->r15, r27|->r16, r27|->r17, r27|->r18, r27|->r24, r27|->r25, r27|->r26, r28|->r0, r28|->r1, r28|->r2, r28|->r12, r28|->r14, r28|->r16, r28|->r17, r28|->r18, r28|->r19, r28|->r22, r28|->r23, r28|->r27, r29|->r0, r29|->r1, r29|->r2, r29|->r3, r29|->r5, r29|->r6, r29|->r8, r29|->r9, r29|->r12, r29|->r14, r29|->r16, r29|->r19, r29|->r20, r29|->r22, r29|->r23, r30|->r3, r30|->r4, r30|->r5, r30|->r7, r30|->r8, r30|->r9, r30|->r15, r30|->r16, r30|->r17, r30|->r18, r30|->r20, r30|->r21, r30|->r24, r30|->r25, r30|->r26, r30|->r27, r31|->r0, r31|->r1, r31|->r6, r31|->r13, r31|->r19, r31|->r21, r31|->r22, r31|->r23, r31|->r28, r31|->r29, r31|->r30, r32|->r0, r32|->r1, r32|->r2, r32|->r3, r32|->r5, r32|->r6, r32|->r7, r32|->r9, r32|->r11, r32|->r12, r32|->r14, r32|->r18, r32|->r19, r32|->r20, r32|->r26, r32|->r29, r32|->r30, r33|->r0, r33|->r1, r33|->r4, r33|->r5, r33|->r7, r33|->r8, r33|->r9, r33|->r10, r33|->r12, r33|->r13, r33|->r15, r33|->r16, r33|->r17, r33|->r18, r33|->r20, r33|->r21, r33|->r22, r33|->r23, r33|->r25, r33|->r29, r33|->r32, r34|->r0, r34|->r6, r34|->r8, r34|->r9, r34|->r13, r34|->r14, r34|->r18, r34|->r20, r34|->r21, r34|->r23, r34|->r24, r34|->r25, r34|->r30, r34|->r31, r34|->r32, r35|->r1, r35|->r2, r35|->r3, r35|->r7, r35|->r13, r35|->r17, r35|->r21, r35|->r22, r35|->r23, r35|->r26, r35|->r27, r35|->r30, r35|->r31, r35|->r32, r35|->r34, r36|->r2, r36|->r4, r36|->r6, r36|->r8, r36|->r9, r36|->r10, r36|->r11, r36|->r14, r36|->r15, r36|->r16, r36|->r17, r36|->r19, r36|->r21, r36|->r22, r36|->r23, r36|->r26, r36|->r27, r36|->r29, r36|->r34, r37|->r2, r37|->r3, r37|->r4, r37|->r5, r37|->r6, r37|->r7, r37|->r9, r37|->r10, r37|->r12, r37|->r13, r37|->r18, r37|->r19, r37|->r20, r37|->r21, r37|->r22, r37|->r26, r37|->r28, r37|->r30, r37|->r31, r37|->r32, r37|->r34, r37|->r36, r38|->r0, r38|->r1, r38|->r3, r38|->r7, r38|->r8, r38|->r9, r38|->r11, r38|->r13, r38|->r15, r38|->r16, r38|->r17, r38|->r18, r38|->r19, r38|->r22, r38|->r27, r38|->r28, r38|->r29, r38|->r31, r38|->r33, r38|->r34, r39|->r4, r39|->r6, r39|->r8, r39|->r9, r39|->r10, r39|->r12, r39|->r14, r39|->r16, r39|->r18, r39|->r19, r39|->r23, r39|->r24, r39|->r26, r39|->r27, r39|->r28, r39|->r30, r39|->r32, r39|->r33, r39|->r34, r39|->r36, r40|->r5, r40|->r9, r40|->r12, r40|->r14, r40|->r15, r40|->r16, r40|->r19, r40|->r21, r40|->r22, r40|->r23, r40|->r25, r40|->r26, r40|->r27, r40|->r31, r40|->r32, r40|->r33, r40|->r36, r41|->r2, r41|->r5, r41|->r11, r41|->r15, r41|->r17, r41|->r22, r41|->r24, r41|->r25, r41|->r27, r41|->r29, r41|->r30, r41|->r33, r41|->r34, r41|->r37, r41|->r38, r41|->r39} &
    rules={rule0|->(rec(su:s40,re:r23,mo:per,pr: 0,co:{c2,c1,c4,c5,c6,c7})), rule1|->(rec(su:s6,re:r10,mo:per,pr: 0,co:{c7,c1,c8,c3})), rule2|->(rec(su:s9,re:r39,mo:per,pr: 1,co:{c1,c3,c4,c8,c5})), rule3|->(rec(su:s22,re:r17,mo:pro,pr: 2,co:{c4,c9})), rule4|->(rec(su:s18,re:r30,mo:pro,pr: 0,co:{c4,c1,c9,c0,c8})), rule5|->(rec(su:s20,re:r39,mo:per,pr: 4,co:{c0,c4,c8})), rule6|->(rec(su:s16,re:r40,mo:per,pr: 0,co:{c9,c3})), rule7|->(rec(su:s24,re:r7,mo:pro,pr: 2,co:{c9,c1,c4,c3,c5,c8,c6,c2})), rule8|->(rec(su:s30,re:r20,mo:pro,pr: 4,co:{c5,c8})), rule9|->(rec(su:s15,re:r7,mo:pro,pr: 3,co:{c5,c1})), rule10|->(rec(su:s38,re:r40,mo:per,pr: 1,co:{c0,c7,c2,c1,c5,c8})), rule11|->(rec(su:s8,re:r1,mo:pro,pr: 1,co:{c4})), rule12|->(rec(su:s11,re:r17,mo:pro,pr: 2,co:{c8}))}

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