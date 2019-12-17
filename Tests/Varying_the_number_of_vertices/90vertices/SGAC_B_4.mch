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
    e_sub={s1|->s0, s2|->s0, s3|->s1, s3|->s2, s4|->s2, s5|->s0, s5|->s4, s6|->s2, s6|->s4, s7|->s0, s7|->s2, s7|->s3, s7|->s4, s7|->s5, s7|->s6, s8|->s2, s8|->s4, s8|->s6, s8|->s7, s9|->s0, s9|->s1, s9|->s2, s9|->s3, s9|->s6, s9|->s7, s10|->s1, s10|->s8, s11|->s1, s11|->s4, s11|->s7, s11|->s10, s12|->s2, s12|->s6, s12|->s7, s12|->s8, s12|->s10, s12|->s11, s13|->s1, s13|->s3, s13|->s6, s13|->s7, s13|->s8, s13|->s9, s13|->s10, s13|->s12, s14|->s0, s14|->s1, s14|->s4, s14|->s5, s14|->s8, s14|->s9, s14|->s10, s14|->s11, s15|->s6, s15|->s7, s15|->s8, s15|->s9, s15|->s12, s15|->s13, s15|->s14, s16|->s0, s16|->s1, s16|->s2, s16|->s3, s16|->s4, s16|->s7, s16|->s8, s16|->s9, s16|->s11, s16|->s15, s17|->s0, s17|->s1, s17|->s2, s17|->s5, s17|->s6, s17|->s7, s17|->s11, s17|->s12, s17|->s14, s17|->s15, s18|->s4, s18|->s5, s18|->s6, s18|->s7, s18|->s8, s18|->s11, s18|->s12, s18|->s14, s18|->s15, s18|->s16, s19|->s5, s19|->s7, s19|->s9, s19|->s11, s19|->s12, s19|->s13, s19|->s14, s19|->s15, s19|->s18, s20|->s2, s20|->s3, s20|->s4, s20|->s7, s20|->s11, s20|->s12, s20|->s13, s20|->s18, s21|->s1, s21|->s2, s21|->s4, s21|->s5, s21|->s6, s22|->s0, s22|->s1, s22|->s2, s22|->s4, s22|->s5, s22|->s6, s22|->s11, s22|->s14, s22|->s15, s22|->s17, s22|->s18, s22|->s19, s22|->s20, s22|->s21, s23|->s4, s23|->s11, s23|->s12, s23|->s17, s23|->s22, s24|->s0, s24|->s1, s24|->s2, s24|->s3, s24|->s8, s24|->s9, s24|->s10, s24|->s11, s24|->s12, s24|->s13, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s20, s25|->s3, s25|->s4, s25|->s5, s25|->s6, s25|->s8, s25|->s10, s25|->s14, s25|->s16, s25|->s19, s26|->s0, s26|->s1, s26|->s2, s26|->s3, s26|->s4, s26|->s5, s26|->s6, s26|->s8, s26|->s9, s26|->s10, s26|->s13, s26|->s14, s26|->s16, s26|->s19, s26|->s20, s26|->s24, s27|->s1, s27|->s5, s27|->s6, s27|->s9, s27|->s13, s27|->s14, s27|->s15, s27|->s19, s27|->s20, s27|->s25, s28|->s1, s28|->s2, s28|->s3, s28|->s6, s28|->s8, s28|->s9, s28|->s10, s28|->s12, s28|->s15, s28|->s16, s28|->s17, s28|->s18, s28|->s20, s28|->s22, s28|->s23, s28|->s25, s28|->s26, s29|->s1, s29|->s2, s29|->s5, s29|->s6, s29|->s7, s29|->s9, s29|->s11, s29|->s14, s29|->s20, s29|->s21, s29|->s22, s29|->s23, s29|->s24, s29|->s28, s30|->s1, s30|->s4, s30|->s8, s30|->s9, s30|->s14, s30|->s17, s30|->s19, s30|->s20, s30|->s23, s30|->s24, s30|->s25, s30|->s29, s31|->s3, s31|->s6, s31|->s10, s31|->s11, s31|->s12, s31|->s13, s31|->s14, s31|->s16, s31|->s17, s31|->s19, s31|->s20, s31|->s25, s31|->s29, s32|->s2, s32|->s7, s32|->s11, s32|->s13, s32|->s19, s32|->s22, s32|->s24, s32|->s25, s32|->s27, s32|->s29, s33|->s1, s33|->s2, s33|->s6, s33|->s8, s33|->s9, s33|->s15, s33|->s19, s33|->s23, s33|->s24, s33|->s27, s33|->s28, s33|->s29, s33|->s30, s33|->s32, s34|->s0, s34|->s2, s34|->s3, s34|->s7, s34|->s9, s34|->s11, s34|->s12, s34|->s14, s34|->s15, s34|->s26, s34|->s29, s34|->s30, s34|->s32, s34|->s33, s35|->s1, s35|->s2, s35|->s4, s35|->s5, s35|->s6, s35|->s8, s35|->s9, s35|->s11, s35|->s12, s35|->s14, s35|->s15, s35|->s20, s35|->s25, s35|->s26, s35|->s27, s35|->s30, s35|->s32, s35|->s33, s35|->s34, s36|->s0, s36|->s1, s36|->s3, s36|->s4, s36|->s5, s36|->s7, s36|->s8, s36|->s10, s36|->s17, s36|->s20, s36|->s21, s36|->s22, s36|->s23, s36|->s24, s36|->s27, s36|->s30, s36|->s32, s36|->s33, s36|->s34, s37|->s2, s37|->s3, s37|->s4, s37|->s6, s37|->s11, s37|->s12, s37|->s13, s37|->s15, s37|->s16, s37|->s25, s37|->s26, s37|->s29, s37|->s30, s37|->s34, s37|->s35, s37|->s36, s38|->s3, s38|->s8, s38|->s10, s38|->s11, s38|->s12, s38|->s15, s38|->s17, s38|->s18, s38|->s25, s38|->s26, s38|->s27, s38|->s29, s38|->s34, s38|->s35, s38|->s36, s39|->s2, s39|->s5, s39|->s9, s39|->s13, s39|->s14, s39|->s15, s39|->s16, s39|->s22, s39|->s27, s39|->s28, s39|->s30, s39|->s33, s40|->s0, s40|->s1, s40|->s5, s40|->s6, s40|->s7, s40|->s9, s40|->s10, s40|->s11, s40|->s15, s40|->s16, s40|->s17, s40|->s19, s40|->s20, s40|->s21, s40|->s22, s40|->s23, s40|->s24, s40|->s25, s40|->s28, s40|->s29, s40|->s30, s40|->s31, s40|->s32, s40|->s34, s40|->s36, s40|->s38, s41|->s1, s41|->s2, s41|->s5, s41|->s6, s41|->s7, s41|->s9, s41|->s11, s41|->s12, s41|->s13, s41|->s17, s41|->s18, s41|->s20, s41|->s22, s41|->s25, s41|->s28, s41|->s29, s41|->s30, s41|->s32, s41|->s35, s41|->s36, s41|->s39, s41|->s40, s42|->s0, s42|->s1, s42|->s2, s42|->s3, s42|->s4, s42|->s8, s42|->s11, s42|->s12, s42|->s13, s42|->s14, s42|->s17, s42|->s19, s42|->s20, s42|->s21, s42|->s24, s42|->s26, s42|->s27, s42|->s28, s42|->s31, s42|->s33, s42|->s35, s42|->s40, s42|->s41, s43|->s1, s43|->s2, s43|->s3, s43|->s11, s43|->s12, s43|->s15, s43|->s19, s43|->s20, s43|->s23, s43|->s25, s43|->s28, s43|->s32, s43|->s35, s43|->s36, s43|->s38, s43|->s39, s43|->s41, s44|->s0, s44|->s2, s44|->s4, s44|->s6, s44|->s7, s44|->s9, s44|->s11, s44|->s13, s44|->s14, s44|->s15, s44|->s16, s44|->s21, s44|->s22, s44|->s25, s44|->s29, s44|->s30, s44|->s31, s44|->s36, s44|->s37, s44|->s38, s44|->s40, s44|->s42} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r3|->r0, r3|->r2, r4|->r0, r4|->r2, r4|->r3, r5|->r1, r6|->r0, r6|->r2, r6|->r4, r7|->r0, r7|->r1, r7|->r5, r7|->r6, r8|->r0, r8|->r1, r8|->r2, r8|->r3, r8|->r5, r8|->r7, r9|->r1, r9|->r4, r9|->r5, r10|->r4, r10|->r5, r10|->r6, r11|->r0, r11|->r3, r11|->r4, r11|->r8, r11|->r9, r11|->r10, r12|->r0, r12|->r1, r12|->r2, r12|->r3, r12|->r7, r12|->r8, r13|->r0, r13|->r1, r13|->r2, r13|->r5, r13|->r8, r13|->r10, r14|->r0, r14|->r1, r14|->r2, r14|->r4, r14|->r5, r14|->r6, r14|->r7, r14|->r8, r14|->r9, r15|->r2, r15|->r4, r15|->r5, r15|->r6, r15|->r7, r15|->r8, r15|->r9, r15|->r10, r15|->r12, r15|->r14, r16|->r1, r16|->r4, r16|->r6, r16|->r7, r16|->r10, r16|->r11, r16|->r14, r17|->r0, r17|->r3, r17|->r4, r17|->r6, r17|->r10, r17|->r13, r17|->r14, r17|->r15, r18|->r0, r18|->r1, r18|->r2, r18|->r4, r18|->r7, r18|->r9, r18|->r12, r18|->r17, r19|->r0, r19|->r2, r19|->r3, r19|->r6, r19|->r11, r19|->r12, r19|->r14, r19|->r15, r19|->r16, r20|->r1, r20|->r3, r20|->r7, r20|->r8, r20|->r11, r20|->r12, r20|->r14, r20|->r15, r20|->r16, r20|->r18, r21|->r0, r21|->r1, r21|->r2, r21|->r7, r21|->r8, r21|->r10, r21|->r11, r21|->r14, r21|->r15, r21|->r16, r21|->r18, r22|->r1, r22|->r4, r22|->r5, r22|->r7, r22|->r8, r22|->r9, r22|->r10, r22|->r16, r22|->r17, r22|->r18, r22|->r21, r23|->r0, r23|->r1, r23|->r2, r23|->r5, r23|->r6, r23|->r10, r23|->r11, r23|->r12, r23|->r13, r23|->r14, r23|->r15, r23|->r16, r23|->r17, r23|->r18, r23|->r19, r23|->r20, r23|->r21, r24|->r3, r24|->r6, r24|->r7, r24|->r8, r24|->r9, r24|->r13, r24|->r14, r24|->r15, r24|->r16, r24|->r18, r24|->r20, r24|->r21, r25|->r1, r25|->r2, r25|->r6, r25|->r7, r25|->r11, r25|->r12, r25|->r13, r25|->r15, r25|->r18, r25|->r19, r25|->r23, r26|->r0, r26|->r2, r26|->r5, r26|->r6, r26|->r7, r26|->r9, r26|->r10, r26|->r12, r26|->r14, r26|->r16, r26|->r17, r26|->r18, r26|->r21, r26|->r22, r26|->r24, r26|->r25, r27|->r0, r27|->r1, r27|->r3, r27|->r5, r27|->r6, r27|->r8, r27|->r10, r27|->r11, r27|->r14, r27|->r16, r27|->r17, r27|->r20, r27|->r22, r27|->r24, r27|->r25, r27|->r26, r28|->r6, r28|->r9, r28|->r10, r28|->r13, r28|->r15, r28|->r16, r28|->r17, r28|->r19, r28|->r20, r28|->r21, r28|->r24, r28|->r26, r28|->r27, r29|->r4, r29|->r5, r29|->r7, r29|->r8, r29|->r10, r29|->r11, r29|->r12, r29|->r13, r29|->r14, r29|->r16, r29|->r17, r29|->r19, r29|->r20, r29|->r25, r29|->r27, r29|->r28, r30|->r0, r30|->r1, r30|->r2, r30|->r3, r30|->r4, r30|->r8, r30|->r9, r30|->r11, r30|->r14, r30|->r17, r30|->r19, r30|->r20, r30|->r22, r30|->r24, r30|->r26, r30|->r27, r30|->r28, r31|->r0, r31|->r1, r31|->r3, r31|->r4, r31|->r5, r31|->r9, r31|->r10, r31|->r11, r31|->r12, r31|->r13, r31|->r19, r31|->r20, r31|->r21, r31|->r22, r31|->r23, r31|->r24, r31|->r29, r31|->r30, r32|->r1, r32|->r2, r32|->r6, r32|->r12, r32|->r14, r32|->r16, r32|->r18, r32|->r20, r32|->r22, r32|->r24, r32|->r25, r32|->r30, r32|->r31, r33|->r0, r33|->r4, r33|->r5, r33|->r6, r33|->r7, r33|->r9, r33|->r11, r33|->r12, r33|->r14, r33|->r16, r33|->r18, r33|->r20, r33|->r21, r33|->r22, r33|->r26, r33|->r29, r34|->r3, r34|->r7, r34|->r9, r34|->r10, r34|->r13, r34|->r14, r34|->r16, r34|->r17, r34|->r19, r34|->r21, r34|->r23, r34|->r25, r34|->r27, r34|->r28, r34|->r29, r34|->r31, r35|->r0, r35|->r1, r35|->r2, r35|->r4, r35|->r7, r35|->r8, r35|->r17, r35|->r18, r35|->r21, r35|->r22, r35|->r26, r35|->r29, r35|->r31, r35|->r34, r36|->r4, r36|->r5, r36|->r7, r36|->r8, r36|->r12, r36|->r13, r36|->r14, r36|->r16, r36|->r17, r36|->r20, r36|->r22, r36|->r23, r36|->r24, r36|->r28, r36|->r31, r36|->r32, r36|->r35, r37|->r8, r37|->r10, r37|->r11, r37|->r14, r37|->r16, r37|->r17, r37|->r18, r37|->r19, r37|->r20, r37|->r21, r37|->r22, r37|->r25, r37|->r26, r37|->r28, r37|->r29, r37|->r32, r37|->r34, r38|->r0, r38|->r1, r38|->r2, r38|->r8, r38|->r9, r38|->r11, r38|->r12, r38|->r13, r38|->r14, r38|->r17, r38|->r18, r38|->r19, r38|->r20, r38|->r21, r38|->r27, r38|->r31, r39|->r1, r39|->r3, r39|->r5, r39|->r10, r39|->r12, r39|->r16, r39|->r17, r39|->r18, r39|->r19, r39|->r20, r39|->r21, r39|->r26, r39|->r28, r39|->r29, r39|->r32, r39|->r33, r39|->r34, r39|->r37, r39|->r38, r40|->r1, r40|->r4, r40|->r7, r40|->r11, r40|->r14, r40|->r15, r40|->r16, r40|->r19, r40|->r20, r40|->r22, r40|->r25, r40|->r26, r40|->r29, r40|->r30, r40|->r31, r40|->r33, r40|->r34, r40|->r39, r41|->r1, r41|->r2, r41|->r5, r41|->r10, r41|->r11, r41|->r13, r41|->r16, r41|->r17, r41|->r19, r41|->r24, r41|->r25, r41|->r26, r41|->r27, r41|->r29, r41|->r30, r41|->r31, r41|->r33, r41|->r35, r41|->r37, r41|->r39, r41|->r40, r42|->r2, r42|->r3, r42|->r6, r42|->r7, r42|->r9, r42|->r12, r42|->r13, r42|->r15, r42|->r16, r42|->r18, r42|->r19, r42|->r20, r42|->r21, r42|->r22, r42|->r24, r42|->r27, r42|->r29, r42|->r31, r42|->r32, r42|->r33, r42|->r34, r42|->r35, r42|->r37, r42|->r39, r43|->r0, r43|->r2, r43|->r4, r43|->r5, r43|->r9, r43|->r13, r43|->r16, r43|->r17, r43|->r18, r43|->r19, r43|->r21, r43|->r24, r43|->r25, r43|->r26, r43|->r31, r43|->r32, r43|->r33, r43|->r36, r43|->r38, r43|->r39, r43|->r41, r43|->r42, r44|->r3, r44|->r6, r44|->r7, r44|->r8, r44|->r9, r44|->r10, r44|->r12, r44|->r15, r44|->r16, r44|->r18, r44|->r20, r44|->r21, r44|->r22, r44|->r25, r44|->r26, r44|->r27, r44|->r29, r44|->r30, r44|->r31, r44|->r32, r44|->r33, r44|->r34, r44|->r35, r44|->r38, r44|->r40, r44|->r43} &
    rules={rule0|->(rec(su:s30,re:r15,mo:per,pr: 1,co:{c7,c9,c8,c4})), rule1|->(rec(su:s20,re:r10,mo:per,pr: 0,co:{c8,c6,c5,c1,c4})), rule2|->(rec(su:s4,re:r36,mo:per,pr: 1,co:{c8,c0})), rule3|->(rec(su:s38,re:r35,mo:per,pr: 3,co:{c2,c6,c9,c1,c7,c4})), rule4|->(rec(su:s41,re:r33,mo:per,pr: 1,co:{c8,c3,c6})), rule5|->(rec(su:s21,re:r38,mo:per,pr: 4,co:{c5,c7,c2,c0,c1,c6})), rule6|->(rec(su:s31,re:r33,mo:per,pr: 0,co:{c1,c3,c8})), rule7|->(rec(su:s17,re:r42,mo:per,pr: 4,co:{c0,c4})), rule8|->(rec(su:s24,re:r8,mo:per,pr: 2,co:{c6,c0,c3,c5,c1,c4})), rule9|->(rec(su:s34,re:r10,mo:per,pr: 0,co:{c0,c7,c9,c2})), rule10|->(rec(su:s40,re:r30,mo:per,pr: 4,co:{c6,c1,c5,c8})), rule11|->(rec(su:s24,re:r40,mo:per,pr: 4,co:{c0})), rule12|->(rec(su:s43,re:r38,mo:per,pr: 0,co:{c9,c2}))}

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