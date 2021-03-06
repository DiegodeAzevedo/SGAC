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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46};
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
    e_sub={s1|->s0, s3|->s1, s4|->s1, s4|->s2, s5|->s0, s5|->s2, s5|->s3, s6|->s0, s6|->s1, s6|->s3, s6|->s4, s6|->s5, s7|->s0, s7|->s1, s7|->s4, s7|->s6, s8|->s1, s8|->s3, s8|->s4, s8|->s5, s9|->s1, s9|->s2, s9|->s5, s9|->s6, s9|->s7, s10|->s1, s10|->s4, s10|->s5, s10|->s6, s11|->s2, s11|->s3, s11|->s5, s11|->s7, s11|->s9, s11|->s10, s12|->s0, s12|->s3, s12|->s9, s12|->s11, s13|->s0, s13|->s1, s13|->s5, s13|->s8, s13|->s11, s13|->s12, s14|->s1, s14|->s3, s14|->s6, s14|->s8, s14|->s10, s14|->s12, s14|->s13, s15|->s2, s15|->s7, s15|->s8, s15|->s9, s15|->s10, s15|->s11, s15|->s14, s16|->s0, s16|->s4, s16|->s5, s16|->s8, s16|->s10, s16|->s12, s16|->s15, s17|->s1, s17|->s2, s17|->s4, s17|->s5, s17|->s8, s17|->s13, s17|->s15, s18|->s0, s18|->s1, s18|->s3, s18|->s4, s18|->s5, s18|->s7, s18|->s8, s18|->s14, s18|->s16, s18|->s17, s19|->s0, s19|->s3, s19|->s4, s19|->s6, s19|->s8, s19|->s13, s19|->s17, s19|->s18, s20|->s0, s20|->s1, s20|->s2, s20|->s11, s20|->s12, s20|->s14, s20|->s17, s20|->s18, s21|->s0, s21|->s2, s21|->s4, s21|->s6, s21|->s11, s21|->s16, s21|->s19, s21|->s20, s22|->s0, s22|->s3, s22|->s5, s22|->s10, s22|->s12, s22|->s13, s22|->s16, s22|->s18, s22|->s20, s22|->s21, s23|->s5, s23|->s6, s23|->s7, s23|->s8, s23|->s9, s23|->s12, s23|->s13, s23|->s14, s23|->s15, s23|->s16, s23|->s17, s23|->s21, s24|->s1, s24|->s2, s24|->s3, s24|->s5, s24|->s6, s24|->s8, s24|->s11, s24|->s12, s24|->s13, s24|->s15, s24|->s16, s24|->s17, s24|->s19, s24|->s20, s24|->s21, s24|->s22, s25|->s0, s25|->s2, s25|->s7, s25|->s10, s25|->s12, s25|->s15, s25|->s17, s25|->s19, s25|->s21, s25|->s23, s25|->s24, s26|->s0, s26|->s2, s26|->s5, s26|->s6, s26|->s12, s26|->s15, s26|->s19, s26|->s22, s26|->s23, s27|->s0, s27|->s1, s27|->s4, s27|->s7, s27|->s9, s27|->s10, s27|->s11, s27|->s15, s27|->s17, s27|->s18, s27|->s20, s27|->s23, s28|->s1, s28|->s2, s28|->s4, s28|->s6, s28|->s7, s28|->s8, s28|->s10, s28|->s11, s28|->s13, s28|->s16, s28|->s19, s28|->s22, s28|->s25, s28|->s26, s28|->s27, s29|->s0, s29|->s4, s29|->s5, s29|->s6, s29|->s7, s29|->s10, s29|->s11, s29|->s13, s29|->s16, s29|->s18, s29|->s19, s29|->s20, s29|->s27, s30|->s1, s30|->s3, s30|->s4, s30|->s8, s30|->s11, s30|->s13, s30|->s14, s30|->s15, s30|->s20, s30|->s24, s30|->s25, s30|->s26, s30|->s27, s30|->s28, s31|->s3, s31|->s4, s31|->s6, s31|->s7, s31|->s11, s31|->s14, s31|->s16, s31|->s17, s31|->s18, s31|->s19, s31|->s20, s31|->s22, s31|->s24, s31|->s25, s31|->s26, s31|->s28, s31|->s29, s32|->s1, s32|->s2, s32|->s3, s32|->s5, s32|->s7, s32|->s10, s32|->s12, s32|->s14, s32|->s16, s32|->s17, s32|->s20, s32|->s29, s32|->s30, s33|->s1, s33|->s2, s33|->s3, s33|->s4, s33|->s5, s33|->s6, s33|->s7, s33|->s10, s33|->s11, s33|->s15, s33|->s16, s33|->s17, s33|->s21, s33|->s22, s33|->s24, s33|->s29, s33|->s30, s34|->s0, s34|->s1, s34|->s3, s34|->s5, s34|->s6, s34|->s12, s34|->s14, s34|->s16, s34|->s17, s34|->s18, s34|->s23, s34|->s24, s34|->s26, s34|->s32, s34|->s33, s35|->s3, s35|->s5, s35|->s6, s35|->s7, s35|->s9, s35|->s10, s35|->s12, s35|->s13, s35|->s14, s35|->s16, s35|->s21, s35|->s22, s35|->s23, s35|->s24, s35|->s26, s35|->s27, s35|->s28, s35|->s32, s35|->s33, s36|->s0, s36|->s1, s36|->s5, s36|->s8, s36|->s15, s36|->s16, s36|->s19, s36|->s22, s36|->s25, s36|->s27, s36|->s29, s36|->s30, s36|->s33, s36|->s34, s36|->s35, s37|->s1, s37|->s2, s37|->s3, s37|->s4, s37|->s5, s37|->s8, s37|->s11, s37|->s13, s37|->s15, s37|->s16, s37|->s17, s37|->s23, s37|->s25, s37|->s27, s37|->s28, s37|->s31, s37|->s33, s37|->s35, s38|->s2, s38|->s3, s38|->s6, s38|->s10, s38|->s12, s38|->s14, s38|->s16, s38|->s17, s38|->s18, s38|->s25, s38|->s26, s38|->s27, s38|->s28, s38|->s30, s38|->s32, s38|->s34, s39|->s0, s39|->s2, s39|->s3, s39|->s5, s39|->s7, s39|->s8, s39|->s13, s39|->s14, s39|->s17, s39|->s19, s39|->s22, s39|->s23, s39|->s24, s39|->s26, s39|->s27, s39|->s28, s39|->s29, s39|->s30, s39|->s31, s39|->s33, s39|->s34, s39|->s35, s39|->s37, s39|->s38, s40|->s3, s40|->s5, s40|->s8, s40|->s12, s40|->s13, s40|->s16, s40|->s18, s40|->s19, s40|->s22, s40|->s27, s40|->s28, s40|->s29, s40|->s31, s40|->s32, s40|->s33, s40|->s36, s40|->s38, s40|->s39, s41|->s0, s41|->s3, s41|->s6, s41|->s7, s41|->s9, s41|->s11, s41|->s15, s41|->s16, s41|->s18, s41|->s19, s41|->s20, s41|->s21, s41|->s23, s41|->s24, s41|->s27, s41|->s28, s41|->s30, s41|->s32, s41|->s34, s41|->s36, s41|->s39, s41|->s40, s42|->s2, s42|->s7, s42|->s8, s42|->s11, s42|->s13, s42|->s14, s42|->s17, s42|->s18, s42|->s19, s42|->s21, s42|->s24, s42|->s31, s42|->s32, s42|->s33, s42|->s35, s42|->s38, s43|->s0, s43|->s4, s43|->s5, s43|->s9, s43|->s10, s43|->s14, s43|->s15, s43|->s16, s43|->s17, s43|->s20, s43|->s21, s43|->s24, s43|->s25, s43|->s27, s43|->s28, s43|->s29, s43|->s31, s43|->s34, s43|->s37, s43|->s41, s44|->s1, s44|->s6, s44|->s8, s44|->s10, s44|->s11, s44|->s12, s44|->s13, s44|->s14, s44|->s17, s44|->s19, s44|->s20, s44|->s21, s44|->s25, s44|->s29, s44|->s30, s44|->s32, s44|->s39, s44|->s40, s44|->s42, s44|->s43, s45|->s0, s45|->s3, s45|->s4, s45|->s5, s45|->s6, s45|->s7, s45|->s9, s45|->s12, s45|->s13, s45|->s15, s45|->s17, s45|->s22, s45|->s23, s45|->s24, s45|->s29, s45|->s34, s45|->s36, s45|->s37, s45|->s38, s45|->s40, s45|->s41, s45|->s42, s45|->s43, s46|->s0, s46|->s2, s46|->s3, s46|->s13, s46|->s14, s46|->s15, s46|->s19, s46|->s21, s46|->s22, s46|->s23, s46|->s29, s46|->s32, s46|->s37, s46|->s39, s46|->s41, s47|->s2, s47|->s5, s47|->s10, s47|->s12, s47|->s13, s47|->s14, s47|->s15, s47|->s20, s47|->s23, s47|->s30, s47|->s35, s47|->s38, s47|->s40, s47|->s44, s47|->s45} &
    e_res={r2|->r0, r2|->r1, r3|->r0, r4|->r1, r4|->r2, r5|->r0, r5|->r1, r6|->r2, r6|->r3, r6|->r4, r7|->r0, r7|->r4, r7|->r5, r8|->r0, r8|->r1, r8|->r2, r8|->r6, r8|->r7, r9|->r1, r9|->r2, r9|->r4, r9|->r6, r10|->r0, r10|->r1, r10|->r3, r10|->r4, r10|->r5, r10|->r7, r10|->r9, r11|->r0, r11|->r2, r11|->r5, r11|->r8, r11|->r9, r11|->r10, r12|->r2, r12|->r8, r12|->r11, r13|->r0, r13|->r1, r13|->r3, r13|->r4, r13|->r5, r13|->r6, r13|->r8, r13|->r9, r13|->r12, r14|->r1, r14|->r2, r14|->r5, r14|->r6, r14|->r7, r14|->r10, r14|->r13, r15|->r1, r15|->r2, r15|->r3, r15|->r4, r15|->r5, r15|->r6, r15|->r7, r15|->r10, r15|->r11, r15|->r12, r15|->r13, r16|->r0, r16|->r2, r16|->r3, r16|->r6, r16|->r10, r16|->r11, r16|->r12, r16|->r13, r16|->r14, r17|->r0, r17|->r2, r17|->r4, r17|->r5, r17|->r7, r17|->r10, r17|->r11, r17|->r14, r17|->r15, r17|->r16, r18|->r1, r18|->r4, r18|->r5, r18|->r9, r18|->r10, r18|->r11, r18|->r13, r18|->r17, r19|->r3, r19|->r7, r19|->r9, r19|->r10, r19|->r11, r19|->r13, r19|->r14, r19|->r15, r19|->r16, r19|->r17, r19|->r18, r20|->r1, r20|->r2, r20|->r4, r20|->r8, r20|->r9, r20|->r10, r20|->r13, r20|->r15, r20|->r16, r20|->r17, r20|->r18, r20|->r19, r21|->r2, r21|->r6, r21|->r8, r21|->r11, r21|->r12, r21|->r17, r22|->r0, r22|->r2, r22|->r6, r22|->r8, r22|->r10, r22|->r11, r22|->r13, r22|->r20, r23|->r1, r23|->r3, r23|->r5, r23|->r6, r23|->r7, r23|->r8, r23|->r9, r23|->r10, r23|->r12, r23|->r13, r23|->r14, r23|->r16, r23|->r17, r23|->r20, r23|->r22, r24|->r0, r24|->r2, r24|->r3, r24|->r7, r24|->r10, r24|->r11, r24|->r16, r24|->r17, r24|->r18, r24|->r21, r24|->r22, r25|->r1, r25|->r4, r25|->r6, r25|->r7, r25|->r8, r25|->r10, r25|->r13, r25|->r14, r25|->r16, r25|->r17, r25|->r18, r25|->r19, r25|->r20, r25|->r24, r26|->r3, r26|->r5, r26|->r6, r26|->r8, r26|->r15, r26|->r18, r26|->r19, r26|->r20, r26|->r22, r26|->r23, r26|->r24, r26|->r25, r27|->r1, r27|->r4, r27|->r11, r27|->r14, r27|->r20, r27|->r23, r27|->r26, r28|->r0, r28|->r1, r28|->r3, r28|->r4, r28|->r5, r28|->r7, r28|->r8, r28|->r11, r28|->r16, r28|->r19, r28|->r20, r28|->r21, r28|->r22, r28|->r24, r28|->r27, r29|->r1, r29|->r5, r29|->r7, r29|->r9, r29|->r10, r29|->r11, r29|->r12, r29|->r14, r29|->r21, r29|->r23, r29|->r24, r29|->r26, r30|->r1, r30|->r4, r30|->r5, r30|->r7, r30|->r8, r30|->r9, r30|->r10, r30|->r12, r30|->r17, r30|->r21, r30|->r22, r30|->r23, r30|->r26, r30|->r27, r30|->r29, r31|->r1, r31|->r6, r31|->r12, r31|->r16, r31|->r19, r31|->r20, r31|->r21, r31|->r26, r31|->r27, r31|->r28, r31|->r29, r32|->r0, r32|->r1, r32|->r5, r32|->r7, r32|->r8, r32|->r9, r32|->r10, r32|->r12, r32|->r13, r32|->r15, r32|->r16, r32|->r18, r32|->r19, r32|->r20, r32|->r21, r32|->r24, r32|->r25, r32|->r26, r32|->r27, r32|->r30, r32|->r31, r33|->r0, r33|->r1, r33|->r2, r33|->r3, r33|->r4, r33|->r8, r33|->r9, r33|->r10, r33|->r13, r33|->r15, r33|->r21, r33|->r24, r33|->r25, r33|->r26, r33|->r27, r33|->r29, r33|->r32, r34|->r1, r34|->r2, r34|->r3, r34|->r5, r34|->r7, r34|->r12, r34|->r16, r34|->r18, r34|->r22, r34|->r25, r34|->r26, r34|->r30, r34|->r31, r35|->r0, r35|->r3, r35|->r4, r35|->r6, r35|->r11, r35|->r14, r35|->r15, r35|->r19, r35|->r22, r35|->r23, r35|->r24, r35|->r27, r35|->r29, r35|->r31, r36|->r2, r36|->r5, r36|->r6, r36|->r7, r36|->r11, r36|->r15, r36|->r16, r36|->r18, r36|->r19, r36|->r20, r36|->r21, r36|->r22, r36|->r23, r36|->r29, r36|->r31, r36|->r32, r37|->r0, r37|->r2, r37|->r4, r37|->r5, r37|->r10, r37|->r11, r37|->r12, r37|->r14, r37|->r15, r37|->r17, r37|->r18, r37|->r19, r37|->r20, r37|->r23, r37|->r24, r37|->r25, r37|->r26, r37|->r27, r37|->r29, r37|->r31, r37|->r35, r37|->r36, r38|->r1, r38|->r2, r38|->r3, r38|->r4, r38|->r6, r38|->r8, r38|->r13, r38|->r16, r38|->r17, r38|->r19, r38|->r20, r38|->r21, r38|->r23, r38|->r26, r38|->r28, r38|->r29, r38|->r31, r38|->r37, r39|->r0, r39|->r3, r39|->r4, r39|->r6, r39|->r7, r39|->r8, r39|->r10, r39|->r12, r39|->r14, r39|->r16, r39|->r18, r39|->r21, r39|->r23, r39|->r24, r39|->r25, r39|->r32, r39|->r34, r39|->r35, r39|->r36, r39|->r38, r40|->r1, r40|->r7, r40|->r8, r40|->r9, r40|->r10, r40|->r11, r40|->r13, r40|->r16, r40|->r17, r40|->r21, r40|->r22, r40|->r23, r40|->r24, r40|->r26, r40|->r27, r40|->r28, r40|->r31, r40|->r33, r40|->r34, r40|->r36, r41|->r1, r41|->r4, r41|->r6, r41|->r8, r41|->r10, r41|->r13, r41|->r14, r41|->r15, r41|->r18, r41|->r23, r41|->r24, r41|->r25, r41|->r28, r41|->r29, r41|->r30, r41|->r31, r41|->r32, r41|->r34, r42|->r1, r42|->r2, r42|->r3, r42|->r8, r42|->r11, r42|->r14, r42|->r19, r42|->r20, r42|->r21, r42|->r22, r42|->r23, r42|->r32, r42|->r33, r42|->r34, r42|->r35, r42|->r36, r42|->r37, r43|->r0, r43|->r1, r43|->r5, r43|->r6, r43|->r7, r43|->r8, r43|->r9, r43|->r12, r43|->r13, r43|->r14, r43|->r18, r43|->r19, r43|->r23, r43|->r26, r43|->r28, r43|->r29, r43|->r31, r43|->r35, r43|->r38, r43|->r39, r43|->r40, r43|->r42, r44|->r1, r44|->r3, r44|->r7, r44|->r8, r44|->r9, r44|->r13, r44|->r17, r44|->r20, r44|->r21, r44|->r26, r44|->r28, r44|->r30, r44|->r31, r44|->r32, r44|->r33, r44|->r34, r44|->r35, r44|->r36, r44|->r38, r44|->r41, r44|->r42, r45|->r0, r45|->r1, r45|->r2, r45|->r3, r45|->r5, r45|->r7, r45|->r8, r45|->r9, r45|->r11, r45|->r18, r45|->r21, r45|->r23, r45|->r25, r45|->r27, r45|->r30, r45|->r34, r45|->r36, r45|->r37, r45|->r38, r45|->r41, r45|->r42, r45|->r43, r45|->r44, r46|->r3, r46|->r6, r46|->r9, r46|->r10, r46|->r11, r46|->r13, r46|->r14, r46|->r15, r46|->r16, r46|->r18, r46|->r24, r46|->r26, r46|->r28, r46|->r31, r46|->r33, r46|->r38, r46|->r40, r46|->r44, r46|->r45} &
    rules={rule0|->(rec(su:s28,re:r45,mo:per,pr: 3,co:{c5,c7,c4,c6,c9,c3})), rule1|->(rec(su:s6,re:r21,mo:pro,pr: 4,co:{c0,c9,c3,c7,c5,c6})), rule2|->(rec(su:s15,re:r12,mo:pro,pr: 3,co:{c1,c9,c0,c8})), rule3|->(rec(su:s44,re:r46,mo:pro,pr: 1,co:{c6,c3,c9})), rule4|->(rec(su:s20,re:r24,mo:pro,pr: 1,co:{c4,c2,c9,c6})), rule5|->(rec(su:s3,re:r10,mo:pro,pr: 1,co:{c1,c7})), rule6|->(rec(su:s20,re:r34,mo:pro,pr: 4,co:{c2,c7,c9,c1,c8,c3})), rule7|->(rec(su:s9,re:r12,mo:per,pr: 3,co:{c1,c6,c5,c0,c4,c3})), rule8|->(rec(su:s41,re:r0,mo:pro,pr: 1,co:{c9,c0,c7})), rule9|->(rec(su:s11,re:r20,mo:per,pr: 0,co:{c9,c0,c1})), rule10|->(rec(su:s24,re:r24,mo:pro,pr: 0,co:{c6,c2})), rule11|->(rec(su:s4,re:r0,mo:pro,pr: 3,co:{c0,c8,c4,c7})), rule12|->(rec(su:s24,re:r16,mo:pro,pr: 1,co:{c7}))}

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