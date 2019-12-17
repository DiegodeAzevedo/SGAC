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
    e_sub={s1|->s0, s3|->s0, s3|->s1, s4|->s1, s4|->s2, s5|->s2, s5|->s3, s5|->s4, s6|->s0, s6|->s3, s6|->s4, s6|->s5, s7|->s0, s7|->s3, s7|->s4, s7|->s6, s8|->s1, s8|->s2, s8|->s5, s9|->s0, s9|->s1, s9|->s3, s9|->s7, s10|->s0, s10|->s2, s10|->s5, s10|->s7, s10|->s9, s11|->s5, s11|->s6, s11|->s8, s11|->s9, s12|->s3, s12|->s4, s12|->s5, s12|->s6, s12|->s7, s12|->s9, s12|->s10, s12|->s11, s13|->s0, s13|->s1, s13|->s4, s13|->s7, s13|->s10, s13|->s12, s14|->s0, s14|->s1, s14|->s2, s14|->s3, s14|->s4, s14|->s7, s14|->s13, s15|->s1, s15|->s2, s15|->s3, s15|->s4, s15|->s5, s15|->s8, s16|->s0, s16|->s3, s16|->s5, s16|->s6, s16|->s7, s16|->s8, s16|->s10, s16|->s13, s16|->s14, s17|->s1, s17|->s3, s17|->s4, s17|->s6, s17|->s10, s17|->s11, s17|->s12, s17|->s14, s18|->s0, s18|->s2, s18|->s3, s18|->s4, s18|->s9, s18|->s10, s18|->s12, s18|->s16, s19|->s0, s19|->s1, s19|->s5, s19|->s6, s19|->s7, s19|->s8, s19|->s18, s20|->s0, s20|->s1, s20|->s3, s20|->s5, s20|->s8, s20|->s10, s20|->s13, s20|->s14, s20|->s15, s20|->s17, s20|->s18, s21|->s1, s21|->s2, s21|->s6, s21|->s8, s21|->s9, s21|->s11, s21|->s12, s21|->s15, s21|->s16, s21|->s19, s21|->s20, s22|->s0, s22|->s1, s22|->s2, s22|->s4, s22|->s5, s22|->s7, s22|->s8, s22|->s9, s22|->s12, s22|->s14, s22|->s15, s22|->s16, s22|->s17, s22|->s20, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s4, s23|->s6, s23|->s11, s23|->s13, s23|->s14, s23|->s15, s23|->s16, s23|->s17, s23|->s18, s23|->s20, s23|->s21, s23|->s22, s24|->s1, s24|->s4, s24|->s7, s24|->s9, s24|->s11, s24|->s12, s24|->s15, s24|->s16, s24|->s19, s24|->s21, s24|->s22, s24|->s23, s25|->s2, s25|->s4, s25|->s7, s25|->s8, s25|->s9, s25|->s13, s25|->s14, s25|->s17, s25|->s18, s25|->s19, s25|->s20, s25|->s21, s25|->s22, s25|->s23, s25|->s24, s26|->s1, s26|->s3, s26|->s4, s26|->s8, s26|->s9, s26|->s11, s26|->s14, s26|->s15, s26|->s16, s26|->s18, s26|->s23, s26|->s24, s26|->s25, s27|->s0, s27|->s7, s27|->s8, s27|->s9, s27|->s10, s27|->s14, s27|->s17, s27|->s22, s27|->s23, s27|->s24, s27|->s25, s27|->s26, s28|->s0, s28|->s3, s28|->s5, s28|->s7, s28|->s10, s28|->s11, s28|->s12, s28|->s14, s28|->s15, s28|->s16, s28|->s17, s28|->s18, s28|->s19, s28|->s20, s28|->s21, s28|->s22, s28|->s24, s28|->s25, s28|->s26, s29|->s2, s29|->s4, s29|->s7, s29|->s8, s29|->s10, s29|->s11, s29|->s13, s29|->s14, s29|->s15, s29|->s16, s29|->s19, s29|->s20, s29|->s21, s29|->s25, s29|->s28, s30|->s1, s30|->s2, s30|->s4, s30|->s5, s30|->s6, s30|->s7, s30|->s11, s30|->s13, s30|->s14, s30|->s15, s30|->s16, s30|->s17, s30|->s18, s30|->s19, s30|->s21, s30|->s24, s30|->s25, s30|->s26, s30|->s27, s31|->s0, s31|->s1, s31|->s2, s31|->s4, s31|->s5, s31|->s7, s31|->s9, s31|->s10, s31|->s14, s31|->s15, s31|->s16, s31|->s17, s31|->s19, s31|->s20, s31|->s22, s31|->s24, s31|->s25, s31|->s27, s31|->s28, s31|->s29, s31|->s30, s32|->s1, s32|->s2, s32|->s3, s32|->s7, s32|->s8, s32|->s9, s32|->s13, s32|->s14, s32|->s18, s32|->s23, s32|->s24, s32|->s25, s32|->s29, s32|->s31, s33|->s0, s33|->s2, s33|->s3, s33|->s5, s33|->s7, s33|->s16, s33|->s19, s33|->s20, s33|->s21, s33|->s25, s33|->s27, s33|->s29, s34|->s1, s34|->s2, s34|->s3, s34|->s4, s34|->s5, s34|->s7, s34|->s8, s34|->s9, s34|->s10, s34|->s11, s34|->s14, s34|->s15, s34|->s17, s34|->s18, s34|->s19, s34|->s22, s34|->s23, s34|->s24, s34|->s26, s34|->s27, s34|->s28, s34|->s30, s34|->s32, s35|->s0, s35|->s2, s35|->s3, s35|->s6, s35|->s7, s35|->s10, s35|->s11, s35|->s14, s35|->s16, s35|->s17, s35|->s21, s35|->s23, s35|->s26, s35|->s27, s35|->s28, s35|->s29, s36|->s0, s36|->s2, s36|->s5, s36|->s6, s36|->s8, s36|->s9, s36|->s13, s36|->s14, s36|->s15, s36|->s17, s36|->s18, s36|->s19, s36|->s21, s36|->s22, s36|->s24, s36|->s25, s36|->s30, s36|->s31, s36|->s32, s36|->s34, s37|->s0, s37|->s2, s37|->s3, s37|->s4, s37|->s6, s37|->s7, s37|->s8, s37|->s10, s37|->s12, s37|->s17, s37|->s19, s37|->s21, s37|->s22, s37|->s24, s37|->s25, s37|->s26, s37|->s28, s37|->s30, s37|->s31, s37|->s32, s37|->s34, s37|->s35, s38|->s2, s38|->s3, s38|->s4, s38|->s6, s38|->s7, s38|->s10, s38|->s11, s38|->s14, s38|->s16, s38|->s18, s38|->s19, s38|->s21, s38|->s22, s38|->s23, s38|->s24, s38|->s25, s38|->s26, s38|->s27, s38|->s28, s38|->s30, s38|->s31, s38|->s32, s38|->s33, s38|->s37, s39|->s3, s39|->s4, s39|->s5, s39|->s8, s39|->s9, s39|->s15, s39|->s17, s39|->s18, s39|->s20, s39|->s21, s39|->s22, s39|->s24, s39|->s25, s39|->s26, s39|->s27, s39|->s30, s39|->s32, s39|->s34, s39|->s35, s39|->s36, s40|->s1, s40|->s3, s40|->s4, s40|->s7, s40|->s11, s40|->s16, s40|->s17, s40|->s18, s40|->s19, s40|->s25, s40|->s28, s40|->s33, s40|->s34, s40|->s39, s41|->s3, s41|->s9, s41|->s11, s41|->s15, s41|->s16, s41|->s17, s41|->s18, s41|->s21, s41|->s23, s41|->s24, s41|->s28, s41|->s29, s41|->s40, s42|->s0, s42|->s1, s42|->s2, s42|->s3, s42|->s5, s42|->s9, s42|->s11, s42|->s12, s42|->s13, s42|->s15, s42|->s22, s42|->s25, s42|->s26, s42|->s27, s42|->s28, s42|->s30, s42|->s31, s42|->s33, s42|->s37, s42|->s39, s42|->s40, s42|->s41, s43|->s0, s43|->s1, s43|->s2, s43|->s4, s43|->s5, s43|->s10, s43|->s11, s43|->s14, s43|->s22, s43|->s24, s43|->s26, s43|->s27, s43|->s28, s43|->s29, s43|->s32, s43|->s36, s43|->s38, s43|->s40, s43|->s41, s43|->s42, s44|->s1, s44|->s2, s44|->s4, s44|->s6, s44|->s7, s44|->s9, s44|->s12, s44|->s14, s44|->s15, s44|->s17, s44|->s18, s44|->s22, s44|->s23, s44|->s24, s44|->s25, s44|->s28, s44|->s30, s44|->s33, s44|->s36, s44|->s37, s44|->s38, s44|->s39, s44|->s40, s44|->s42} &
    e_res={r1|->r0, r2|->r0, r3|->r0, r3|->r1, r3|->r2, r4|->r0, r5|->r3, r5|->r4, r6|->r0, r6|->r1, r6|->r2, r6|->r4, r7|->r3, r7|->r4, r7|->r5, r8|->r1, r8|->r2, r8|->r3, r8|->r6, r8|->r7, r9|->r2, r9|->r3, r9|->r5, r9|->r8, r10|->r3, r10|->r4, r10|->r5, r10|->r6, r10|->r8, r11|->r0, r11|->r1, r11|->r2, r11|->r3, r11|->r7, r11|->r8, r12|->r1, r12|->r2, r12|->r3, r12|->r4, r12|->r6, r12|->r7, r12|->r9, r12|->r10, r13|->r0, r13|->r1, r13|->r6, r13|->r9, r13|->r11, r14|->r1, r14|->r2, r14|->r6, r14|->r7, r14|->r8, r14|->r11, r14|->r12, r14|->r13, r15|->r0, r15|->r2, r15|->r5, r15|->r6, r15|->r7, r15|->r8, r15|->r9, r15|->r12, r15|->r13, r15|->r14, r16|->r4, r16|->r5, r16|->r6, r16|->r8, r16|->r11, r16|->r12, r17|->r2, r17|->r3, r17|->r4, r17|->r8, r17|->r10, r17|->r13, r17|->r15, r17|->r16, r18|->r0, r18|->r6, r18|->r8, r18|->r9, r18|->r11, r18|->r13, r18|->r14, r18|->r15, r18|->r16, r19|->r1, r19|->r4, r19|->r5, r19|->r7, r19|->r8, r19|->r11, r19|->r12, r19|->r13, r19|->r14, r19|->r15, r19|->r18, r20|->r1, r20|->r6, r20|->r8, r20|->r11, r20|->r15, r20|->r16, r20|->r18, r21|->r1, r21|->r2, r21|->r4, r21|->r5, r21|->r6, r21|->r11, r21|->r15, r21|->r18, r21|->r20, r22|->r0, r22|->r1, r22|->r3, r22|->r4, r22|->r8, r22|->r9, r22|->r12, r22|->r15, r22|->r16, r22|->r19, r22|->r20, r22|->r21, r23|->r3, r23|->r6, r23|->r8, r23|->r13, r23|->r16, r23|->r17, r23|->r18, r23|->r20, r24|->r0, r24|->r1, r24|->r2, r24|->r5, r24|->r6, r24|->r7, r24|->r8, r24|->r10, r24|->r11, r24|->r12, r24|->r16, r24|->r17, r24|->r18, r24|->r21, r24|->r22, r25|->r0, r25|->r2, r25|->r3, r25|->r4, r25|->r5, r25|->r9, r25|->r10, r25|->r11, r25|->r13, r25|->r14, r25|->r17, r25|->r18, r25|->r20, r25|->r21, r25|->r22, r25|->r23, r26|->r1, r26|->r4, r26|->r8, r26|->r9, r26|->r10, r26|->r11, r26|->r13, r26|->r14, r26|->r17, r26|->r18, r26|->r21, r26|->r22, r26|->r24, r26|->r25, r27|->r0, r27|->r1, r27|->r4, r27|->r5, r27|->r6, r27|->r7, r27|->r9, r27|->r10, r27|->r11, r27|->r13, r27|->r15, r27|->r17, r27|->r18, r27|->r19, r27|->r20, r27|->r21, r27|->r24, r27|->r25, r28|->r8, r28|->r9, r28|->r11, r28|->r12, r28|->r15, r28|->r17, r28|->r18, r28|->r20, r28|->r22, r28|->r25, r28|->r27, r29|->r0, r29|->r6, r29|->r7, r29|->r8, r29|->r9, r29|->r13, r29|->r16, r29|->r19, r29|->r20, r29|->r21, r29|->r22, r29|->r23, r29|->r26, r29|->r27, r30|->r1, r30|->r2, r30|->r3, r30|->r4, r30|->r6, r30|->r7, r30|->r8, r30|->r9, r30|->r12, r30|->r18, r30|->r20, r30|->r21, r30|->r24, r30|->r27, r30|->r28, r30|->r29, r31|->r1, r31|->r2, r31|->r3, r31|->r6, r31|->r7, r31|->r9, r31|->r12, r31|->r15, r31|->r16, r31|->r18, r31|->r19, r31|->r20, r31|->r21, r31|->r22, r31|->r23, r31|->r25, r31|->r26, r31|->r27, r31|->r29, r31|->r30, r32|->r1, r32|->r4, r32|->r5, r32|->r6, r32|->r7, r32|->r11, r32|->r16, r32|->r17, r32|->r19, r32|->r20, r32|->r24, r32|->r25, r32|->r27, r32|->r28, r32|->r30, r32|->r31, r33|->r0, r33|->r2, r33|->r3, r33|->r4, r33|->r10, r33|->r11, r33|->r12, r33|->r15, r33|->r16, r33|->r17, r33|->r18, r33|->r19, r33|->r21, r33|->r22, r33|->r23, r33|->r25, r33|->r26, r33|->r28, r33|->r29, r33|->r30, r34|->r0, r34|->r3, r34|->r5, r34|->r6, r34|->r7, r34|->r8, r34|->r9, r34|->r13, r34|->r14, r34|->r15, r34|->r16, r34|->r17, r34|->r18, r34|->r19, r34|->r20, r34|->r22, r34|->r23, r34|->r28, r34|->r32, r34|->r33, r35|->r0, r35|->r2, r35|->r3, r35|->r9, r35|->r12, r35|->r13, r35|->r15, r35|->r16, r35|->r17, r35|->r18, r35|->r19, r35|->r20, r35|->r21, r35|->r22, r35|->r23, r35|->r24, r35|->r25, r35|->r28, r35|->r29, r35|->r31, r35|->r32, r35|->r33, r35|->r34, r36|->r0, r36|->r6, r36|->r7, r36|->r19, r36|->r21, r36|->r23, r36|->r24, r36|->r25, r36|->r26, r36|->r27, r36|->r28, r36|->r29, r36|->r30, r36|->r33, r36|->r35, r37|->r1, r37|->r2, r37|->r3, r37|->r7, r37|->r8, r37|->r9, r37|->r11, r37|->r13, r37|->r15, r37|->r17, r37|->r18, r37|->r25, r37|->r28, r37|->r32, r37|->r35, r37|->r36, r38|->r1, r38|->r4, r38|->r5, r38|->r6, r38|->r7, r38|->r9, r38|->r10, r38|->r11, r38|->r12, r38|->r18, r38|->r19, r38|->r21, r38|->r22, r38|->r24, r38|->r26, r38|->r27, r38|->r28, r38|->r31, r38|->r32, r38|->r33, r38|->r34, r38|->r35, r38|->r36, r39|->r0, r39|->r2, r39|->r3, r39|->r5, r39|->r6, r39|->r9, r39|->r15, r39|->r18, r39|->r20, r39|->r21, r39|->r22, r39|->r24, r39|->r25, r39|->r27, r39|->r31, r39|->r32, r39|->r34, r39|->r37, r40|->r1, r40|->r3, r40|->r7, r40|->r10, r40|->r11, r40|->r12, r40|->r17, r40|->r18, r40|->r19, r40|->r23, r40|->r24, r40|->r25, r40|->r26, r40|->r27, r40|->r28, r40|->r30, r40|->r32, r40|->r33, r40|->r38, r41|->r0, r41|->r1, r41|->r2, r41|->r8, r41|->r9, r41|->r10, r41|->r11, r41|->r12, r41|->r15, r41|->r16, r41|->r19, r41|->r21, r41|->r26, r41|->r28, r41|->r30, r41|->r36, r41|->r37, r41|->r38, r42|->r0, r42|->r1, r42|->r2, r42|->r3, r42|->r4, r42|->r5, r42|->r6, r42|->r7, r42|->r8, r42|->r9, r42|->r10, r42|->r11, r42|->r12, r42|->r14, r42|->r15, r42|->r16, r42|->r17, r42|->r18, r42|->r19, r42|->r22, r42|->r23, r42|->r24, r42|->r27, r42|->r28, r42|->r29, r42|->r30, r42|->r31, r42|->r32, r42|->r34, r42|->r35, r42|->r36, r42|->r39, r43|->r1, r43|->r2, r43|->r3, r43|->r5, r43|->r6, r43|->r7, r43|->r8, r43|->r10, r43|->r11, r43|->r12, r43|->r13, r43|->r14, r43|->r15, r43|->r17, r43|->r18, r43|->r19, r43|->r21, r43|->r22, r43|->r23, r43|->r25, r43|->r26, r43|->r27, r43|->r30, r43|->r35, r43|->r36, r43|->r41, r43|->r42, r44|->r1, r44|->r2, r44|->r3, r44|->r6, r44|->r7, r44|->r10, r44|->r11, r44|->r14, r44|->r17, r44|->r19, r44|->r23, r44|->r24, r44|->r26, r44|->r31, r44|->r32, r44|->r38, r44|->r40, r44|->r41, r44|->r43} &
    rules={rule0|->(rec(su:s38,re:r10,mo:pro,pr: 3,co:{c9,c6,c2,c5,c1,c7})), rule1|->(rec(su:s32,re:r3,mo:pro,pr: 1,co:{c2,c9})), rule2|->(rec(su:s1,re:r3,mo:per,pr: 1,co:{c1,c4,c6,c3})), rule3|->(rec(su:s37,re:r1,mo:pro,pr: 3,co:{c4,c2,c9})), rule4|->(rec(su:s7,re:r16,mo:pro,pr: 2,co:{c4,c9,c0,c2,c1,c8})), rule5|->(rec(su:s40,re:r20,mo:per,pr: 2,co:{c6,c9,c1,c3,c7,c8,c4})), rule6|->(rec(su:s18,re:r6,mo:per,pr: 2,co:{c0,c1,c5,c2})), rule7|->(rec(su:s36,re:r13,mo:pro,pr: 1,co:{c9,c6,c4})), rule8|->(rec(su:s5,re:r33,mo:pro,pr: 4,co:{c5,c3,c2})), rule9|->(rec(su:s7,re:r24,mo:per,pr: 0,co:{c9,c8,c4,c5,c2,c3})), rule10|->(rec(su:s25,re:r5,mo:per,pr: 3,co:{c4})), rule11|->(rec(su:s4,re:r40,mo:pro,pr: 1,co:{c6,c2,c0,c9,c5})), rule12|->(rec(su:s43,re:r7,mo:per,pr: 2,co:{c5,c0,c8,c7,c2,c9}))}

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