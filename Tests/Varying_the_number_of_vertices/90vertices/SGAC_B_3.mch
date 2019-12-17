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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44};
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
    e_sub={s1|->s0, s2|->s1, s3|->s1, s3|->s2, s4|->s1, s5|->s2, s5|->s4, s6|->s2, s6|->s3, s7|->s0, s7|->s3, s7|->s5, s8|->s0, s8|->s2, s8|->s3, s8|->s4, s8|->s7, s9|->s0, s9|->s4, s9|->s5, s9|->s6, s9|->s8, s10|->s2, s10|->s3, s10|->s4, s10|->s6, s10|->s7, s11|->s2, s11|->s3, s11|->s6, s11|->s7, s11|->s8, s11|->s10, s12|->s0, s12|->s2, s12|->s4, s12|->s5, s12|->s8, s13|->s0, s13|->s2, s13|->s3, s13|->s5, s13|->s6, s13|->s7, s13|->s8, s13|->s11, s13|->s12, s14|->s0, s14|->s3, s14|->s4, s14|->s6, s14|->s9, s14|->s10, s14|->s11, s14|->s12, s15|->s2, s15|->s3, s15|->s4, s15|->s5, s15|->s6, s15|->s7, s15|->s8, s15|->s14, s16|->s1, s16|->s2, s16|->s3, s16|->s4, s16|->s5, s16|->s7, s16|->s8, s16|->s10, s17|->s0, s17|->s1, s17|->s3, s17|->s6, s17|->s8, s17|->s10, s17|->s11, s17|->s13, s17|->s14, s17|->s15, s17|->s16, s18|->s0, s18|->s1, s18|->s3, s18|->s5, s18|->s6, s18|->s8, s18|->s13, s18|->s14, s18|->s15, s18|->s16, s18|->s17, s19|->s1, s19|->s6, s19|->s7, s19|->s9, s19|->s12, s19|->s14, s19|->s17, s19|->s18, s20|->s1, s20|->s2, s20|->s3, s20|->s5, s20|->s6, s20|->s7, s20|->s11, s20|->s12, s20|->s14, s20|->s15, s20|->s16, s20|->s18, s21|->s1, s21|->s2, s21|->s3, s21|->s4, s21|->s6, s21|->s8, s21|->s11, s21|->s14, s21|->s15, s21|->s16, s21|->s19, s21|->s20, s22|->s1, s22|->s2, s22|->s5, s22|->s6, s22|->s7, s22|->s8, s22|->s10, s22|->s12, s22|->s15, s22|->s16, s22|->s17, s22|->s18, s22|->s19, s22|->s20, s22|->s21, s23|->s2, s23|->s6, s23|->s7, s23|->s8, s23|->s12, s23|->s16, s23|->s18, s23|->s19, s23|->s20, s24|->s2, s24|->s3, s24|->s4, s24|->s5, s24|->s7, s24|->s12, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s20, s24|->s23, s25|->s1, s25|->s3, s25|->s4, s25|->s5, s25|->s8, s25|->s11, s25|->s12, s25|->s15, s25|->s16, s25|->s18, s25|->s22, s25|->s23, s25|->s24, s26|->s5, s26|->s8, s26|->s9, s26|->s10, s26|->s11, s26|->s12, s26|->s13, s26|->s19, s26|->s21, s26|->s23, s26|->s24, s27|->s0, s27|->s4, s27|->s5, s27|->s6, s27|->s7, s27|->s9, s27|->s12, s27|->s13, s27|->s14, s27|->s15, s27|->s17, s27|->s19, s27|->s20, s27|->s21, s27|->s23, s27|->s25, s28|->s0, s28|->s2, s28|->s3, s28|->s4, s28|->s5, s28|->s6, s28|->s8, s28|->s9, s28|->s12, s28|->s13, s28|->s15, s28|->s20, s28|->s24, s28|->s25, s28|->s26, s29|->s1, s29|->s4, s29|->s6, s29|->s13, s29|->s14, s29|->s15, s29|->s19, s29|->s20, s29|->s21, s29|->s23, s29|->s24, s29|->s27, s30|->s0, s30|->s3, s30|->s9, s30|->s10, s30|->s14, s30|->s15, s30|->s18, s30|->s21, s30|->s22, s30|->s23, s30|->s24, s30|->s26, s30|->s29, s31|->s1, s31|->s2, s31|->s9, s31|->s10, s31|->s11, s31|->s13, s31|->s20, s31|->s21, s31|->s22, s31|->s23, s31|->s26, s31|->s28, s32|->s2, s32|->s4, s32|->s5, s32|->s7, s32|->s8, s32|->s9, s32|->s10, s32|->s13, s32|->s14, s32|->s15, s32|->s16, s32|->s20, s32|->s21, s32|->s22, s32|->s24, s32|->s25, s32|->s29, s32|->s30, s32|->s31, s33|->s0, s33|->s2, s33|->s3, s33|->s6, s33|->s9, s33|->s12, s33|->s13, s33|->s14, s33|->s18, s33|->s19, s33|->s21, s33|->s27, s33|->s29, s33|->s30, s33|->s32, s34|->s1, s34|->s3, s34|->s4, s34|->s9, s34|->s11, s34|->s13, s34|->s14, s34|->s15, s34|->s16, s34|->s18, s34|->s19, s34|->s22, s34|->s23, s34|->s27, s34|->s28, s34|->s29, s34|->s31, s35|->s0, s35|->s6, s35|->s7, s35|->s9, s35|->s11, s35|->s13, s35|->s14, s35|->s15, s35|->s16, s35|->s17, s35|->s19, s35|->s20, s35|->s22, s35|->s25, s35|->s30, s35|->s31, s35|->s33, s35|->s34, s36|->s0, s36|->s1, s36|->s2, s36|->s3, s36|->s4, s36|->s5, s36|->s6, s36|->s7, s36|->s9, s36|->s10, s36|->s11, s36|->s13, s36|->s15, s36|->s17, s36|->s18, s36|->s20, s36|->s21, s36|->s22, s36|->s23, s36|->s26, s36|->s29, s36|->s30, s36|->s32, s36|->s34, s36|->s35, s37|->s0, s37|->s1, s37|->s2, s37|->s3, s37|->s5, s37|->s8, s37|->s10, s37|->s11, s37|->s13, s37|->s14, s37|->s15, s37|->s16, s37|->s17, s37|->s18, s37|->s22, s37|->s23, s37|->s26, s37|->s27, s37|->s29, s37|->s31, s37|->s35, s38|->s0, s38|->s1, s38|->s2, s38|->s4, s38|->s6, s38|->s7, s38|->s8, s38|->s13, s38|->s16, s38|->s18, s38|->s21, s38|->s25, s38|->s29, s38|->s30, s38|->s32, s38|->s36, s39|->s2, s39|->s3, s39|->s4, s39|->s5, s39|->s8, s39|->s9, s39|->s11, s39|->s12, s39|->s16, s39|->s20, s39|->s22, s39|->s24, s39|->s26, s39|->s27, s39|->s29, s39|->s30, s39|->s31, s39|->s34, s39|->s36, s39|->s38, s40|->s4, s40|->s5, s40|->s8, s40|->s9, s40|->s10, s40|->s11, s40|->s12, s40|->s13, s40|->s15, s40|->s20, s40|->s21, s40|->s22, s40|->s26, s40|->s27, s40|->s29, s40|->s34, s40|->s35, s40|->s38, s40|->s39, s41|->s1, s41|->s2, s41|->s4, s41|->s10, s41|->s11, s41|->s12, s41|->s16, s41|->s20, s41|->s21, s41|->s22, s41|->s23, s41|->s25, s41|->s26, s41|->s27, s41|->s28, s41|->s30, s41|->s31, s41|->s32, s41|->s34, s41|->s38, s41|->s39, s42|->s6, s42|->s8, s42|->s9, s42|->s10, s42|->s13, s42|->s15, s42|->s16, s42|->s17, s42|->s18, s42|->s21, s42|->s22, s42|->s23, s42|->s28, s42|->s30, s42|->s32, s42|->s34, s42|->s35, s42|->s37, s42|->s40, s43|->s0, s43|->s1, s43|->s4, s43|->s5, s43|->s6, s43|->s8, s43|->s13, s43|->s14, s43|->s18, s43|->s19, s43|->s21, s43|->s22, s43|->s26, s43|->s27, s43|->s28, s43|->s30, s43|->s31, s43|->s32, s43|->s33, s43|->s35, s43|->s37, s43|->s38, s43|->s40, s43|->s41, s44|->s2, s44|->s6, s44|->s7, s44|->s8, s44|->s10, s44|->s13, s44|->s14, s44|->s15, s44|->s18, s44|->s21, s44|->s22, s44|->s24, s44|->s25, s44|->s27, s44|->s28, s44|->s30, s44|->s32, s44|->s33, s44|->s35, s44|->s39, s44|->s42} &
    e_res={r2|->r1, r3|->r0, r3|->r1, r3|->r2, r4|->r0, r4|->r1, r4|->r3, r5|->r0, r5|->r2, r5|->r4, r6|->r1, r6|->r2, r6|->r3, r7|->r1, r7|->r3, r8|->r3, r8|->r4, r9|->r0, r9|->r1, r9|->r4, r9|->r5, r9|->r7, r9|->r8, r10|->r1, r10|->r4, r10|->r5, r10|->r8, r10|->r9, r11|->r1, r11|->r3, r11|->r4, r11|->r6, r11|->r8, r12|->r0, r12|->r2, r12|->r6, r12|->r7, r13|->r2, r13|->r5, r13|->r6, r13|->r7, r13|->r10, r14|->r0, r14|->r1, r14|->r2, r14|->r3, r14|->r6, r14|->r7, r14|->r9, r14|->r11, r14|->r12, r15|->r3, r15|->r6, r15|->r7, r15|->r10, r15|->r11, r15|->r13, r15|->r14, r16|->r2, r16|->r5, r16|->r6, r16|->r7, r16|->r8, r16|->r10, r16|->r11, r16|->r12, r16|->r13, r16|->r14, r17|->r0, r17|->r3, r17|->r5, r17|->r6, r17|->r9, r17|->r10, r18|->r1, r18|->r4, r18|->r7, r18|->r8, r18|->r9, r18|->r12, r18|->r15, r19|->r0, r19|->r1, r19|->r7, r19|->r8, r19|->r12, r19|->r14, r20|->r0, r20|->r3, r20|->r5, r20|->r6, r20|->r9, r20|->r10, r20|->r12, r20|->r13, r20|->r14, r20|->r18, r20|->r19, r21|->r0, r21|->r2, r21|->r6, r21|->r7, r21|->r8, r21|->r10, r21|->r14, r21|->r16, r21|->r17, r21|->r19, r22|->r1, r22|->r2, r22|->r5, r22|->r7, r22|->r11, r22|->r12, r22|->r13, r22|->r17, r22|->r18, r23|->r0, r23|->r3, r23|->r4, r23|->r9, r23|->r10, r23|->r11, r23|->r13, r23|->r15, r23|->r16, r24|->r9, r24|->r11, r24|->r12, r24|->r13, r24|->r14, r24|->r15, r24|->r19, r24|->r20, r24|->r21, r24|->r22, r25|->r2, r25|->r4, r25|->r5, r25|->r7, r25|->r8, r25|->r9, r25|->r10, r25|->r12, r25|->r13, r25|->r14, r25|->r15, r25|->r17, r25|->r20, r25|->r22, r25|->r23, r26|->r0, r26|->r2, r26|->r4, r26|->r5, r26|->r7, r26|->r8, r26|->r10, r26|->r17, r26|->r21, r26|->r23, r27|->r0, r27|->r9, r27|->r10, r27|->r11, r27|->r12, r27|->r15, r27|->r16, r27|->r19, r27|->r20, r27|->r25, r27|->r26, r28|->r1, r28|->r2, r28|->r5, r28|->r6, r28|->r7, r28|->r8, r28|->r9, r28|->r11, r28|->r12, r28|->r14, r28|->r16, r28|->r19, r28|->r21, r28|->r25, r28|->r26, r29|->r0, r29|->r1, r29|->r2, r29|->r3, r29|->r4, r29|->r5, r29|->r9, r29|->r10, r29|->r12, r29|->r14, r29|->r16, r29|->r17, r29|->r19, r29|->r21, r29|->r22, r29|->r25, r30|->r7, r30|->r8, r30|->r9, r30|->r10, r30|->r12, r30|->r14, r30|->r18, r30|->r19, r30|->r21, r30|->r23, r30|->r24, r30|->r26, r30|->r27, r30|->r28, r31|->r3, r31|->r6, r31|->r9, r31|->r12, r31|->r13, r31|->r18, r31|->r19, r31|->r21, r31|->r22, r31|->r24, r32|->r1, r32|->r4, r32|->r6, r32|->r8, r32|->r9, r32|->r10, r32|->r14, r32|->r15, r32|->r16, r32|->r19, r32|->r20, r32|->r23, r32|->r24, r32|->r26, r32|->r29, r32|->r30, r32|->r31, r33|->r0, r33|->r6, r33|->r7, r33|->r8, r33|->r9, r33|->r10, r33|->r11, r33|->r12, r33|->r13, r33|->r15, r33|->r20, r33|->r22, r33|->r24, r33|->r30, r33|->r32, r34|->r0, r34|->r1, r34|->r4, r34|->r6, r34|->r8, r34|->r9, r34|->r10, r34|->r11, r34|->r15, r34|->r16, r34|->r17, r34|->r18, r34|->r21, r34|->r23, r34|->r25, r34|->r27, r34|->r28, r34|->r29, r34|->r31, r34|->r33, r35|->r0, r35|->r2, r35|->r4, r35|->r11, r35|->r13, r35|->r16, r35|->r17, r35|->r21, r35|->r22, r35|->r28, r35|->r30, r35|->r31, r35|->r32, r35|->r33, r35|->r34, r36|->r0, r36|->r3, r36|->r6, r36|->r8, r36|->r10, r36|->r12, r36|->r13, r36|->r15, r36|->r16, r36|->r17, r36|->r18, r36|->r20, r36|->r23, r36|->r24, r36|->r26, r36|->r27, r36|->r28, r36|->r29, r36|->r30, r36|->r32, r36|->r34, r37|->r0, r37|->r2, r37|->r3, r37|->r5, r37|->r6, r37|->r8, r37|->r9, r37|->r10, r37|->r14, r37|->r19, r37|->r20, r37|->r22, r37|->r24, r37|->r25, r37|->r26, r37|->r28, r37|->r29, r37|->r33, r38|->r0, r38|->r2, r38|->r4, r38|->r5, r38|->r6, r38|->r8, r38|->r9, r38|->r10, r38|->r11, r38|->r12, r38|->r16, r38|->r17, r38|->r19, r38|->r20, r38|->r21, r38|->r22, r38|->r23, r38|->r24, r38|->r25, r38|->r26, r38|->r29, r38|->r30, r38|->r31, r38|->r32, r38|->r33, r38|->r35, r39|->r3, r39|->r4, r39|->r5, r39|->r7, r39|->r9, r39|->r10, r39|->r12, r39|->r15, r39|->r19, r39|->r20, r39|->r21, r39|->r22, r39|->r24, r39|->r25, r39|->r28, r39|->r29, r39|->r30, r39|->r32, r39|->r33, r39|->r36, r39|->r38, r40|->r0, r40|->r1, r40|->r2, r40|->r3, r40|->r4, r40|->r5, r40|->r6, r40|->r8, r40|->r9, r40|->r14, r40|->r15, r40|->r16, r40|->r17, r40|->r18, r40|->r20, r40|->r22, r40|->r23, r40|->r25, r40|->r27, r40|->r28, r40|->r29, r40|->r34, r40|->r39, r41|->r0, r41|->r1, r41|->r2, r41|->r7, r41|->r13, r41|->r16, r41|->r21, r41|->r25, r41|->r28, r41|->r32, r41|->r33, r41|->r36, r41|->r38, r41|->r40, r42|->r6, r42|->r7, r42|->r8, r42|->r11, r42|->r13, r42|->r14, r42|->r15, r42|->r21, r42|->r24, r42|->r25, r42|->r26, r42|->r28, r42|->r29, r42|->r30, r42|->r31, r42|->r35, r42|->r36, r42|->r37, r42|->r39, r42|->r40, r43|->r0, r43|->r3, r43|->r5, r43|->r7, r43|->r10, r43|->r11, r43|->r12, r43|->r13, r43|->r15, r43|->r18, r43|->r19, r43|->r23, r43|->r24, r43|->r25, r43|->r30, r43|->r31, r43|->r32, r43|->r35, r43|->r37, r43|->r38, r44|->r4, r44|->r5, r44|->r6, r44|->r8, r44|->r10, r44|->r11, r44|->r14, r44|->r15, r44|->r18, r44|->r21, r44|->r22, r44|->r23, r44|->r24, r44|->r25, r44|->r27, r44|->r29, r44|->r33, r44|->r34, r44|->r35, r44|->r40, r44|->r41, r44|->r43} &
    rules={rule0|->(rec(su:s3,re:r11,mo:pro,pr: 2,co:{c2,c5,c3,c4,c1,c9})), rule1|->(rec(su:s17,re:r13,mo:per,pr: 2,co:{c4,c2,c6,c7,c5,c9,c1})), rule2|->(rec(su:s2,re:r16,mo:pro,pr: 3,co:{c5,c6,c2,c3})), rule3|->(rec(su:s33,re:r2,mo:per,pr: 0,co:{c1})), rule4|->(rec(su:s29,re:r3,mo:pro,pr: 4,co:{c1})), rule5|->(rec(su:s6,re:r27,mo:per,pr: 1,co:{c1,c0,c3,c8,c5,c7,c9})), rule6|->(rec(su:s4,re:r14,mo:per,pr: 3,co:{c3})), rule7|->(rec(su:s39,re:r15,mo:per,pr: 3,co:{c8,c1,c2,c0,c4,c6})), rule8|->(rec(su:s21,re:r36,mo:per,pr: 3,co:{c2,c1,c5,c8,c0})), rule9|->(rec(su:s11,re:r16,mo:pro,pr: 3,co:{c0,c9,c5,c3,c2,c7,c1})), rule10|->(rec(su:s23,re:r38,mo:pro,pr: 1,co:{c7})), rule11|->(rec(su:s8,re:r40,mo:per,pr: 0,co:{c4,c2,c3,c7})), rule12|->(rec(su:s11,re:r5,mo:per,pr: 4,co:{c6,c7,c0,c1}))}

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