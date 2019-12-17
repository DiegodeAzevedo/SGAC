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
    e_sub={s3|->s0, s3|->s2, s4|->s0, s4|->s2, s4|->s3, s5|->s0, s5|->s2, s5|->s3, s5|->s4, s6|->s0, s6|->s4, s7|->s2, s7|->s3, s8|->s3, s8|->s4, s8|->s5, s9|->s0, s9|->s2, s9|->s3, s9|->s6, s9|->s7, s9|->s8, s10|->s2, s10|->s7, s11|->s0, s11|->s2, s11|->s3, s11|->s7, s11|->s8, s11|->s9, s12|->s0, s12|->s2, s12|->s3, s12|->s4, s12|->s5, s12|->s8, s12|->s10, s12|->s11, s13|->s0, s13|->s3, s13|->s6, s13|->s7, s13|->s10, s13|->s12, s14|->s0, s14|->s1, s14|->s2, s14|->s4, s14|->s6, s14|->s12, s15|->s0, s15|->s1, s15|->s3, s15|->s4, s15|->s5, s15|->s7, s15|->s9, s15|->s12, s15|->s13, s16|->s0, s16|->s8, s16|->s10, s16|->s12, s16|->s14, s16|->s15, s17|->s0, s17|->s1, s17|->s2, s17|->s4, s17|->s5, s17|->s12, s17|->s14, s17|->s16, s18|->s1, s18|->s2, s18|->s3, s18|->s5, s18|->s6, s18|->s11, s18|->s13, s18|->s14, s18|->s17, s19|->s1, s19|->s2, s19|->s3, s19|->s4, s19|->s7, s19|->s8, s19|->s10, s19|->s11, s19|->s12, s19|->s13, s19|->s17, s19|->s18, s20|->s0, s20|->s2, s20|->s7, s20|->s8, s20|->s9, s20|->s10, s20|->s11, s20|->s12, s20|->s13, s20|->s15, s20|->s17, s20|->s19, s21|->s2, s21|->s3, s21|->s7, s21|->s8, s21|->s12, s21|->s13, s21|->s16, s21|->s20, s22|->s0, s22|->s2, s22|->s4, s22|->s6, s22|->s8, s22|->s9, s22|->s12, s22|->s17, s22|->s20, s22|->s21, s23|->s0, s23|->s1, s23|->s2, s23|->s7, s23|->s8, s23|->s11, s23|->s13, s23|->s14, s23|->s16, s23|->s17, s23|->s18, s23|->s21, s24|->s0, s24|->s2, s24|->s3, s24|->s4, s24|->s5, s24|->s6, s24|->s7, s24|->s9, s24|->s10, s24|->s13, s24|->s14, s24|->s15, s24|->s16, s24|->s18, s24|->s19, s24|->s20, s24|->s21, s24|->s22, s25|->s0, s25|->s1, s25|->s2, s25|->s3, s25|->s5, s25|->s8, s25|->s9, s25|->s11, s25|->s12, s25|->s15, s25|->s16, s25|->s17, s25|->s18, s25|->s19, s25|->s24, s26|->s0, s26|->s2, s26|->s4, s26|->s8, s26|->s9, s26|->s12, s26|->s20, s26|->s22, s26|->s23, s27|->s0, s27|->s4, s27|->s6, s27|->s7, s27|->s8, s27|->s9, s27|->s13, s27|->s15, s27|->s16, s27|->s17, s27|->s18, s27|->s21, s27|->s22, s27|->s23, s27|->s25, s27|->s26, s28|->s3, s28|->s4, s28|->s5, s28|->s6, s28|->s7, s28|->s9, s28|->s15, s28|->s20, s28|->s25, s28|->s26, s28|->s27, s29|->s0, s29|->s4, s29|->s5, s29|->s7, s29|->s8, s29|->s15, s29|->s17, s29|->s24, s29|->s25, s29|->s28, s30|->s0, s30|->s7, s30|->s8, s30|->s11, s30|->s14, s30|->s15, s30|->s17, s30|->s18, s30|->s23, s30|->s24, s30|->s25, s30|->s26, s30|->s29, s31|->s1, s31|->s3, s31|->s4, s31|->s6, s31|->s7, s31|->s8, s31|->s10, s31|->s11, s31|->s12, s31|->s13, s31|->s14, s31|->s15, s31|->s16, s31|->s17, s31|->s22, s31|->s27, s31|->s29, s31|->s30, s32|->s0, s32|->s3, s32|->s5, s32|->s7, s32|->s8, s32|->s11, s32|->s12, s32|->s14, s32|->s15, s32|->s16, s32|->s17, s32|->s20, s32|->s22, s32|->s24, s32|->s27, s32|->s28, s33|->s1, s33|->s2, s33|->s4, s33|->s5, s33|->s7, s33|->s9, s33|->s11, s33|->s15, s33|->s16, s33|->s17, s33|->s20, s33|->s21, s33|->s26, s33|->s28, s33|->s30, s33|->s31, s34|->s0, s34|->s1, s34|->s5, s34|->s6, s34|->s8, s34|->s9, s34|->s11, s34|->s12, s34|->s13, s34|->s14, s34|->s16, s34|->s17, s34|->s19, s34|->s20, s34|->s22, s34|->s26, s34|->s29, s34|->s30, s34|->s31, s34|->s32, s35|->s0, s35|->s2, s35|->s3, s35|->s5, s35|->s7, s35|->s8, s35|->s9, s35|->s10, s35|->s11, s35|->s14, s35|->s15, s35|->s16, s35|->s24, s35|->s25, s35|->s26, s35|->s27, s35|->s31, s35|->s32, s35|->s34, s36|->s0, s36|->s1, s36|->s3, s36|->s4, s36|->s5, s36|->s7, s36|->s9, s36|->s11, s36|->s14, s36|->s23, s36|->s24, s36|->s25, s36|->s26, s36|->s27, s36|->s30, s36|->s32, s36|->s33, s36|->s34, s37|->s0, s37|->s2, s37|->s3, s37|->s4, s37|->s5, s37|->s8, s37|->s11, s37|->s13, s37|->s16, s37|->s20, s37|->s21, s37|->s25, s37|->s26, s37|->s27, s37|->s31, s37|->s32, s37|->s34, s37|->s35, s37|->s36, s38|->s0, s38|->s1, s38|->s2, s38|->s3, s38|->s5, s38|->s6, s38|->s7, s38|->s9, s38|->s13, s38|->s15, s38|->s19, s38|->s23, s38|->s24, s38|->s28, s38|->s30, s38|->s31, s38|->s32, s38|->s34, s38|->s35, s39|->s0, s39|->s1, s39|->s3, s39|->s4, s39|->s7, s39|->s8, s39|->s11, s39|->s13, s39|->s15, s39|->s16, s39|->s18, s39|->s19, s39|->s22, s39|->s27, s39|->s28, s39|->s31, s39|->s32, s39|->s38, s40|->s0, s40|->s3, s40|->s8, s40|->s10, s40|->s11, s40|->s12, s40|->s14, s40|->s16, s40|->s17, s40|->s20, s40|->s23, s40|->s24, s40|->s28, s40|->s29, s40|->s35, s40|->s37, s40|->s38, s40|->s39, s41|->s0, s41|->s1, s41|->s2, s41|->s4, s41|->s6, s41|->s8, s41|->s9, s41|->s11, s41|->s15, s41|->s16, s41|->s19, s41|->s20, s41|->s21, s41|->s24, s41|->s26, s41|->s27, s41|->s32, s41|->s33, s41|->s36, s41|->s38, s41|->s39, s41|->s40, s42|->s0, s42|->s4, s42|->s5, s42|->s6, s42|->s7, s42|->s10, s42|->s11, s42|->s13, s42|->s14, s42|->s15, s42|->s16, s42|->s17, s42|->s18, s42|->s19, s42|->s20, s42|->s21, s42|->s25, s42|->s26, s42|->s27, s42|->s29, s42|->s31, s42|->s32, s42|->s33, s42|->s36, s42|->s39, s42|->s40, s42|->s41, s43|->s5, s43|->s8, s43|->s9, s43|->s13, s43|->s14, s43|->s15, s43|->s17, s43|->s21, s43|->s22, s43|->s28, s43|->s30, s43|->s34, s43|->s36, s43|->s38, s43|->s39, s43|->s41, s43|->s42, s44|->s0, s44|->s5, s44|->s9, s44|->s11, s44|->s12, s44|->s13, s44|->s14, s44|->s16, s44|->s17, s44|->s19, s44|->s24, s44|->s27, s44|->s28, s44|->s31, s44|->s32, s44|->s33, s44|->s37, s44|->s41, s45|->s0, s45|->s1, s45|->s4, s45|->s7, s45|->s8, s45|->s9, s45|->s12, s45|->s14, s45|->s19, s45|->s20, s45|->s22, s45|->s23, s45|->s24, s45|->s26, s45|->s28, s45|->s33, s45|->s36, s45|->s38, s45|->s42, s46|->s5, s46|->s6, s46|->s7, s46|->s9, s46|->s19, s46|->s20, s46|->s21, s46|->s26, s46|->s28, s46|->s29, s46|->s31, s46|->s32, s46|->s33, s46|->s36, s46|->s37, s46|->s40, s46|->s43, s46|->s44, s47|->s0, s47|->s3, s47|->s4, s47|->s5, s47|->s9, s47|->s13, s47|->s16, s47|->s19, s47|->s20, s47|->s21, s47|->s25, s47|->s26, s47|->s28, s47|->s29, s47|->s30, s47|->s34, s47|->s39, s47|->s42, s47|->s43, s47|->s45} &
    e_res={r1|->r0, r2|->r0, r2|->r1, r3|->r0, r3|->r1, r4|->r1, r4|->r3, r5|->r1, r5|->r3, r6|->r0, r6|->r4, r6|->r5, r7|->r4, r7|->r5, r8|->r2, r8|->r3, r8|->r4, r8|->r7, r9|->r0, r9|->r1, r9|->r2, r9|->r3, r9|->r4, r9|->r5, r9|->r6, r9|->r7, r10|->r0, r10|->r2, r10|->r4, r10|->r7, r11|->r1, r11|->r2, r11|->r4, r11|->r5, r11|->r9, r12|->r3, r12|->r8, r12|->r9, r12|->r10, r12|->r11, r13|->r1, r13|->r2, r13|->r3, r13|->r4, r13|->r5, r13|->r7, r13|->r8, r13|->r9, r13|->r10, r14|->r0, r14|->r1, r14|->r2, r14|->r4, r14|->r6, r14|->r10, r15|->r0, r15|->r3, r15|->r4, r15|->r5, r15|->r6, r15|->r7, r15|->r9, r15|->r10, r16|->r3, r16|->r7, r16|->r8, r16|->r11, r17|->r4, r17|->r5, r17|->r6, r17|->r7, r17|->r8, r17|->r10, r17|->r12, r17|->r13, r17|->r14, r18|->r1, r18|->r4, r18|->r5, r18|->r6, r18|->r9, r18|->r10, r18|->r11, r18|->r12, r18|->r13, r19|->r1, r19|->r5, r19|->r6, r19|->r7, r19|->r9, r19|->r10, r19|->r11, r19|->r12, r19|->r15, r19|->r17, r19|->r18, r20|->r1, r20|->r4, r20|->r7, r20|->r9, r20|->r12, r20|->r13, r20|->r14, r20|->r16, r20|->r17, r20|->r18, r20|->r19, r21|->r0, r21|->r1, r21|->r2, r21|->r3, r21|->r4, r21|->r5, r21|->r6, r21|->r7, r21|->r10, r21|->r12, r21|->r14, r21|->r15, r21|->r17, r21|->r18, r21|->r19, r22|->r0, r22|->r2, r22|->r3, r22|->r5, r22|->r6, r22|->r7, r22|->r12, r22|->r13, r22|->r15, r22|->r16, r22|->r17, r22|->r19, r22|->r21, r23|->r0, r23|->r9, r23|->r11, r23|->r13, r23|->r14, r23|->r17, r23|->r20, r24|->r0, r24|->r2, r24|->r7, r24|->r11, r24|->r12, r24|->r14, r24|->r16, r24|->r19, r24|->r23, r25|->r0, r25|->r3, r25|->r5, r25|->r11, r25|->r14, r25|->r17, r25|->r18, r25|->r19, r25|->r22, r25|->r23, r25|->r24, r26|->r0, r26|->r1, r26|->r5, r26|->r8, r26|->r12, r26|->r14, r26|->r15, r26|->r17, r26|->r18, r26|->r23, r27|->r0, r27|->r3, r27|->r4, r27|->r6, r27|->r7, r27|->r9, r27|->r10, r27|->r12, r27|->r16, r27|->r18, r27|->r20, r27|->r21, r27|->r24, r28|->r1, r28|->r2, r28|->r5, r28|->r13, r28|->r15, r28|->r16, r28|->r18, r28|->r21, r28|->r24, r28|->r26, r28|->r27, r29|->r0, r29|->r2, r29|->r3, r29|->r4, r29|->r5, r29|->r6, r29|->r9, r29|->r11, r29|->r12, r29|->r20, r29|->r21, r29|->r22, r29|->r24, r29|->r26, r29|->r28, r30|->r0, r30|->r7, r30|->r9, r30|->r12, r30|->r14, r30|->r16, r30|->r23, r30|->r24, r30|->r26, r30|->r29, r31|->r0, r31|->r1, r31|->r2, r31|->r3, r31|->r7, r31|->r9, r31|->r10, r31|->r11, r31|->r15, r31|->r19, r31|->r22, r31|->r24, r31|->r25, r31|->r27, r31|->r28, r31|->r30, r32|->r2, r32|->r4, r32|->r6, r32|->r7, r32|->r8, r32|->r9, r32|->r13, r32|->r16, r32|->r17, r32|->r19, r32|->r20, r32|->r21, r32|->r22, r32|->r23, r32|->r25, r32|->r26, r32|->r27, r32|->r28, r32|->r31, r33|->r0, r33|->r3, r33|->r4, r33|->r6, r33|->r9, r33|->r10, r33|->r17, r33|->r18, r33|->r20, r33|->r21, r33|->r23, r33|->r24, r33|->r25, r33|->r26, r33|->r27, r33|->r30, r33|->r32, r34|->r4, r34|->r5, r34|->r10, r34|->r11, r34|->r14, r34|->r17, r34|->r19, r34|->r20, r34|->r21, r34|->r22, r34|->r23, r34|->r24, r34|->r26, r34|->r29, r34|->r31, r35|->r0, r35|->r1, r35|->r2, r35|->r3, r35|->r5, r35|->r6, r35|->r11, r35|->r12, r35|->r13, r35|->r15, r35|->r17, r35|->r19, r35|->r21, r35|->r26, r35|->r28, r35|->r30, r35|->r31, r35|->r33, r35|->r34, r36|->r1, r36|->r4, r36|->r6, r36|->r7, r36|->r8, r36|->r12, r36|->r14, r36|->r16, r36|->r17, r36|->r19, r36|->r21, r36|->r23, r36|->r24, r36|->r25, r36|->r26, r36|->r27, r36|->r28, r36|->r32, r36|->r33, r37|->r0, r37|->r2, r37|->r3, r37|->r6, r37|->r7, r37|->r9, r37|->r11, r37|->r17, r37|->r18, r37|->r19, r37|->r23, r37|->r24, r37|->r27, r37|->r29, r37|->r30, r37|->r36, r38|->r1, r38|->r4, r38|->r10, r38|->r12, r38|->r13, r38|->r14, r38|->r15, r38|->r17, r38|->r19, r38|->r20, r38|->r21, r38|->r23, r38|->r26, r38|->r29, r38|->r30, r38|->r31, r38|->r32, r38|->r36, r38|->r37, r39|->r0, r39|->r1, r39|->r5, r39|->r9, r39|->r12, r39|->r13, r39|->r14, r39|->r15, r39|->r16, r39|->r21, r39|->r24, r39|->r26, r39|->r28, r39|->r31, r39|->r32, r39|->r35, r39|->r37, r39|->r38, r40|->r1, r40|->r3, r40|->r6, r40|->r7, r40|->r9, r40|->r12, r40|->r13, r40|->r15, r40|->r21, r40|->r22, r40|->r26, r40|->r27, r40|->r29, r40|->r30, r40|->r34, r40|->r35, r40|->r38, r40|->r39, r41|->r2, r41|->r5, r41|->r6, r41|->r7, r41|->r8, r41|->r9, r41|->r10, r41|->r11, r41|->r12, r41|->r13, r41|->r14, r41|->r16, r41|->r17, r41|->r26, r41|->r28, r41|->r29, r41|->r30, r41|->r32, r41|->r33, r41|->r35, r41|->r36, r41|->r38, r41|->r39, r42|->r2, r42|->r3, r42|->r6, r42|->r7, r42|->r8, r42|->r9, r42|->r15, r42|->r16, r42|->r18, r42|->r19, r42|->r21, r42|->r26, r42|->r27, r42|->r29, r42|->r30, r42|->r31, r42|->r32, r42|->r33, r42|->r38, r42|->r39, r42|->r40, r42|->r41, r43|->r5, r43|->r9, r43|->r15, r43|->r19, r43|->r20, r43|->r23, r43|->r24, r43|->r27, r43|->r28, r43|->r31, r43|->r32, r43|->r34, r43|->r38, r43|->r40, r43|->r41, r44|->r0, r44|->r6, r44|->r7, r44|->r9, r44|->r11, r44|->r12, r44|->r13, r44|->r14, r44|->r17, r44|->r21, r44|->r22, r44|->r24, r44|->r25, r44|->r28, r44|->r30, r44|->r35, r44|->r38, r44|->r39, r44|->r40, r44|->r41, r45|->r0, r45|->r3, r45|->r4, r45|->r10, r45|->r14, r45|->r17, r45|->r19, r45|->r23, r45|->r24, r45|->r25, r45|->r26, r45|->r27, r45|->r28, r45|->r30, r45|->r32, r45|->r33, r45|->r35, r45|->r36, r45|->r39, r45|->r40, r45|->r42, r45|->r43, r45|->r44, r46|->r1, r46|->r4, r46|->r5, r46|->r6, r46|->r7, r46|->r8, r46|->r9, r46|->r11, r46|->r12, r46|->r16, r46|->r19, r46|->r23, r46|->r24, r46|->r26, r46|->r27, r46|->r28, r46|->r29, r46|->r32, r46|->r37, r46|->r39, r46|->r40} &
    rules={rule0|->(rec(su:s11,re:r15,mo:per,pr: 4,co:{c9,c0,c8,c6})), rule1|->(rec(su:s41,re:r33,mo:pro,pr: 0,co:{c3,c6,c2,c0})), rule2|->(rec(su:s37,re:r34,mo:pro,pr: 1,co:{c7,c0,c1,c5})), rule3|->(rec(su:s46,re:r1,mo:pro,pr: 0,co:{c3,c2})), rule4|->(rec(su:s16,re:r25,mo:per,pr: 2,co:{c4,c6})), rule5|->(rec(su:s1,re:r45,mo:pro,pr: 4,co:{c2,c4,c3})), rule6|->(rec(su:s29,re:r37,mo:pro,pr: 1,co:{c9,c0,c6,c8,c5})), rule7|->(rec(su:s31,re:r24,mo:per,pr: 4,co:{c2,c5,c6,c3})), rule8|->(rec(su:s38,re:r45,mo:per,pr: 2,co:{c6,c7,c8,c1,c0})), rule9|->(rec(su:s30,re:r0,mo:pro,pr: 4,co:{c5,c4,c1,c3})), rule10|->(rec(su:s22,re:r40,mo:pro,pr: 1,co:{c9,c7,c5,c3,c6,c4})), rule11|->(rec(su:s3,re:r44,mo:pro,pr: 2,co:{c4,c9,c6,c7})), rule12|->(rec(su:s2,re:r22,mo:pro,pr: 4,co:{c6,c3}))}

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