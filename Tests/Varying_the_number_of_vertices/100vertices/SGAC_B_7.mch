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
    V_SUB={s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54};
    /*resource vertex type*/
    V_RES={r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54};
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
    e_sub={s1|->s0, s2|->s0, s3|->s0, s3|->s2, s5|->s1, s5|->s3, s6|->s1, s6|->s3, s6|->s5, s7|->s1, s7|->s3, s7|->s4, s7|->s5, s8|->s0, s8|->s1, s8|->s3, s8|->s4, s9|->s0, s9|->s2, s9|->s4, s9|->s6, s10|->s1, s10|->s2, s10|->s3, s10|->s6, s10|->s8, s10|->s9, s11|->s1, s11|->s4, s11|->s5, s11|->s6, s11|->s9, s11|->s10, s12|->s0, s12|->s2, s12|->s5, s12|->s6, s12|->s7, s12|->s8, s12|->s10, s13|->s0, s13|->s1, s13|->s4, s13|->s10, s14|->s1, s14|->s3, s14|->s5, s14|->s6, s14|->s8, s14|->s10, s14|->s11, s14|->s12, s14|->s13, s15|->s0, s15|->s3, s15|->s5, s15|->s6, s15|->s7, s15|->s9, s15|->s11, s15|->s12, s15|->s14, s16|->s0, s16|->s1, s16|->s6, s16|->s7, s16|->s8, s16|->s10, s16|->s12, s16|->s13, s17|->s1, s17|->s4, s17|->s6, s17|->s7, s17|->s9, s17|->s10, s17|->s13, s17|->s16, s18|->s0, s18|->s2, s18|->s3, s18|->s4, s18|->s5, s18|->s6, s18|->s7, s18|->s8, s18|->s9, s18|->s10, s18|->s13, s18|->s14, s18|->s16, s18|->s17, s19|->s0, s19|->s2, s19|->s3, s19|->s4, s19|->s5, s19|->s6, s19|->s7, s19|->s8, s19|->s10, s19|->s11, s19|->s15, s19|->s16, s19|->s18, s20|->s0, s20|->s1, s20|->s5, s20|->s8, s20|->s9, s20|->s12, s20|->s16, s20|->s18, s21|->s0, s21|->s1, s21|->s2, s21|->s10, s21|->s14, s21|->s16, s21|->s17, s21|->s19, s22|->s2, s22|->s4, s22|->s5, s22|->s8, s22|->s9, s22|->s11, s22|->s12, s22|->s16, s22|->s19, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s4, s23|->s5, s23|->s7, s23|->s9, s23|->s11, s23|->s12, s23|->s13, s23|->s16, s23|->s17, s23|->s18, s23|->s19, s23|->s21, s23|->s22, s24|->s1, s24|->s6, s24|->s11, s24|->s12, s24|->s13, s24|->s15, s24|->s18, s24|->s19, s24|->s22, s24|->s23, s25|->s0, s25|->s1, s25|->s2, s25|->s3, s25|->s5, s25|->s8, s25|->s9, s25|->s10, s25|->s11, s25|->s13, s25|->s14, s25|->s15, s25|->s19, s25|->s20, s26|->s1, s26|->s2, s26|->s3, s26|->s6, s26|->s9, s26|->s11, s26|->s12, s26|->s14, s26|->s15, s26|->s17, s26|->s18, s26|->s20, s26|->s23, s26|->s24, s26|->s25, s27|->s0, s27|->s1, s27|->s2, s27|->s3, s27|->s4, s27|->s5, s27|->s8, s27|->s9, s27|->s10, s27|->s16, s27|->s18, s27|->s19, s27|->s20, s27|->s22, s27|->s23, s27|->s24, s27|->s26, s28|->s0, s28|->s3, s28|->s7, s28|->s9, s28|->s10, s28|->s12, s28|->s15, s28|->s16, s28|->s17, s28|->s18, s28|->s19, s28|->s20, s28|->s22, s28|->s25, s28|->s26, s28|->s27, s29|->s0, s29|->s3, s29|->s6, s29|->s7, s29|->s8, s29|->s9, s29|->s17, s29|->s18, s29|->s19, s29|->s23, s29|->s24, s29|->s25, s29|->s27, s29|->s28, s30|->s1, s30|->s7, s30|->s8, s30|->s9, s30|->s10, s30|->s14, s30|->s16, s30|->s17, s30|->s18, s30|->s19, s30|->s21, s30|->s22, s30|->s28, s31|->s0, s31|->s3, s31|->s4, s31|->s5, s31|->s9, s31|->s10, s31|->s12, s31|->s14, s31|->s16, s31|->s17, s31|->s19, s31|->s20, s31|->s21, s31|->s22, s31|->s23, s31|->s25, s31|->s29, s32|->s0, s32|->s3, s32|->s5, s32|->s6, s32|->s7, s32|->s8, s32|->s11, s32|->s14, s32|->s21, s32|->s24, s32|->s26, s32|->s27, s32|->s29, s33|->s0, s33|->s2, s33|->s4, s33|->s5, s33|->s7, s33|->s9, s33|->s10, s33|->s11, s33|->s13, s33|->s15, s33|->s16, s33|->s18, s33|->s20, s33|->s21, s33|->s23, s33|->s27, s33|->s28, s34|->s1, s34|->s3, s34|->s5, s34|->s6, s34|->s7, s34|->s14, s34|->s16, s34|->s17, s34|->s20, s34|->s24, s34|->s25, s34|->s27, s34|->s29, s34|->s30, s34|->s31, s34|->s33, s35|->s0, s35|->s1, s35|->s3, s35|->s5, s35|->s7, s35|->s8, s35|->s9, s35|->s10, s35|->s13, s35|->s14, s35|->s15, s35|->s16, s35|->s19, s35|->s20, s35|->s21, s35|->s22, s35|->s23, s35|->s25, s35|->s29, s35|->s30, s35|->s31, s35|->s34, s36|->s4, s36|->s6, s36|->s8, s36|->s10, s36|->s13, s36|->s15, s36|->s16, s36|->s19, s36|->s22, s36|->s24, s36|->s26, s36|->s29, s36|->s31, s36|->s35, s37|->s2, s37|->s5, s37|->s7, s37|->s10, s37|->s14, s37|->s15, s37|->s16, s37|->s17, s37|->s19, s37|->s22, s37|->s23, s37|->s24, s37|->s25, s37|->s28, s37|->s30, s37|->s31, s37|->s32, s37|->s35, s37|->s36, s38|->s0, s38|->s1, s38|->s4, s38|->s5, s38|->s6, s38|->s7, s38|->s8, s38|->s10, s38|->s11, s38|->s15, s38|->s16, s38|->s18, s38|->s19, s38|->s20, s38|->s21, s38|->s24, s38|->s31, s38|->s35, s38|->s37, s39|->s1, s39|->s2, s39|->s3, s39|->s5, s39|->s6, s39|->s7, s39|->s11, s39|->s13, s39|->s15, s39|->s16, s39|->s17, s39|->s18, s39|->s21, s39|->s24, s39|->s27, s39|->s28, s39|->s32, s39|->s33, s39|->s34, s39|->s36, s39|->s37, s39|->s38, s40|->s1, s40|->s4, s40|->s5, s40|->s9, s40|->s10, s40|->s12, s40|->s13, s40|->s14, s40|->s15, s40|->s20, s40|->s21, s40|->s22, s40|->s23, s40|->s24, s40|->s30, s40|->s32, s40|->s33, s40|->s37, s40|->s38, s40|->s39, s41|->s0, s41|->s1, s41|->s2, s41|->s4, s41|->s8, s41|->s9, s41|->s11, s41|->s13, s41|->s16, s41|->s19, s41|->s22, s41|->s23, s41|->s24, s41|->s28, s41|->s29, s41|->s31, s41|->s33, s41|->s34, s41|->s35, s41|->s36, s41|->s38, s41|->s40, s42|->s1, s42|->s2, s42|->s3, s42|->s4, s42|->s5, s42|->s6, s42|->s10, s42|->s17, s42|->s18, s42|->s19, s42|->s20, s42|->s22, s42|->s23, s42|->s26, s42|->s27, s42|->s28, s42|->s30, s42|->s33, s42|->s35, s42|->s36, s42|->s41, s43|->s0, s43|->s3, s43|->s4, s43|->s7, s43|->s10, s43|->s14, s43|->s16, s43|->s17, s43|->s21, s43|->s22, s43|->s24, s43|->s25, s43|->s26, s43|->s28, s43|->s31, s43|->s32, s43|->s34, s43|->s35, s43|->s37, s43|->s38, s43|->s39, s43|->s42, s44|->s1, s44|->s2, s44|->s3, s44|->s4, s44|->s5, s44|->s9, s44|->s10, s44|->s11, s44|->s12, s44|->s13, s44|->s18, s44|->s19, s44|->s22, s44|->s26, s44|->s28, s44|->s30, s44|->s31, s44|->s34, s44|->s36, s44|->s37, s44|->s38, s45|->s0, s45|->s4, s45|->s5, s45|->s7, s45|->s12, s45|->s13, s45|->s16, s45|->s20, s45|->s21, s45|->s26, s45|->s27, s45|->s29, s45|->s31, s45|->s32, s45|->s34, s45|->s36, s45|->s38, s45|->s39, s45|->s40, s45|->s42, s45|->s43, s45|->s44, s46|->s4, s46|->s9, s46|->s13, s46|->s16, s46|->s17, s46|->s18, s46|->s21, s46|->s25, s46|->s28, s46|->s29, s46|->s33, s46|->s35, s46|->s36, s46|->s37, s46|->s39, s46|->s43, s47|->s2, s47|->s3, s47|->s7, s47|->s10, s47|->s11, s47|->s12, s47|->s13, s47|->s14, s47|->s15, s47|->s17, s47|->s18, s47|->s24, s47|->s27, s47|->s28, s47|->s29, s47|->s30, s47|->s34, s47|->s35, s47|->s38, s47|->s40, s47|->s41, s47|->s42, s47|->s43, s47|->s44, s47|->s45, s47|->s46, s48|->s0, s48|->s2, s48|->s3, s48|->s5, s48|->s6, s48|->s7, s48|->s8, s48|->s12, s48|->s14, s48|->s15, s48|->s17, s48|->s18, s48|->s21, s48|->s23, s48|->s25, s48|->s26, s48|->s30, s48|->s31, s48|->s32, s48|->s35, s48|->s36, s48|->s37, s48|->s38, s48|->s41, s48|->s43, s49|->s0, s49|->s2, s49|->s4, s49|->s5, s49|->s6, s49|->s7, s49|->s11, s49|->s15, s49|->s16, s49|->s17, s49|->s18, s49|->s19, s49|->s21, s49|->s27, s49|->s28, s49|->s29, s49|->s30, s49|->s31, s49|->s33, s49|->s34, s49|->s39, s49|->s40, s49|->s41, s49|->s44, s49|->s46, s50|->s0, s50|->s1, s50|->s2, s50|->s3, s50|->s6, s50|->s7, s50|->s9, s50|->s10, s50|->s12, s50|->s13, s50|->s15, s50|->s16, s50|->s19, s50|->s22, s50|->s24, s50|->s25, s50|->s29, s50|->s30, s50|->s31, s50|->s34, s50|->s35, s50|->s38, s50|->s41, s50|->s43, s50|->s48, s50|->s49, s51|->s3, s51|->s4, s51|->s6, s51|->s8, s51|->s9, s51|->s10, s51|->s11, s51|->s12, s51|->s13, s51|->s16, s51|->s17, s51|->s18, s51|->s20, s51|->s21, s51|->s22, s51|->s23, s51|->s24, s51|->s25, s51|->s26, s51|->s31, s51|->s32, s51|->s34, s51|->s35, s51|->s36, s51|->s39, s51|->s40, s51|->s42, s51|->s44, s51|->s45, s51|->s46, s51|->s47, s51|->s48, s51|->s49, s52|->s1, s52|->s2, s52|->s3, s52|->s7, s52|->s8, s52|->s10, s52|->s11, s52|->s13, s52|->s15, s52|->s16, s52|->s17, s52|->s19, s52|->s22, s52|->s26, s52|->s28, s52|->s30, s52|->s33, s52|->s34, s52|->s35, s52|->s39, s52|->s40, s52|->s41, s52|->s42, s52|->s43, s52|->s46, s52|->s49, s52|->s50, s52|->s51, s53|->s0, s53|->s2, s53|->s4, s53|->s6, s53|->s8, s53|->s9, s53|->s11, s53|->s12, s53|->s15, s53|->s16, s53|->s20, s53|->s21, s53|->s23, s53|->s24, s53|->s26, s53|->s27, s53|->s33, s53|->s35, s53|->s46, s53|->s47, s53|->s48, s53|->s49, s54|->s3, s54|->s5, s54|->s6, s54|->s8, s54|->s9, s54|->s11, s54|->s12, s54|->s13, s54|->s15, s54|->s16, s54|->s17, s54|->s18, s54|->s19, s54|->s27, s54|->s28, s54|->s31, s54|->s33, s54|->s35, s54|->s36, s54|->s38, s54|->s39, s54|->s41, s54|->s43, s54|->s45, s54|->s49, s54|->s52, s54|->s53} &
    e_res={r2|->r0, r2|->r1, r3|->r1, r3|->r2, r4|->r1, r4|->r2, r5|->r1, r5|->r3, r5|->r4, r6|->r3, r7|->r2, r7|->r3, r7|->r4, r7|->r5, r7|->r6, r8|->r2, r8|->r4, r8|->r6, r8|->r7, r9|->r0, r9|->r3, r9|->r4, r9|->r6, r9|->r7, r9|->r8, r10|->r0, r10|->r4, r11|->r1, r11|->r2, r11|->r5, r11|->r7, r11|->r8, r11|->r9, r11|->r10, r12|->r3, r12|->r4, r12|->r5, r12|->r7, r12|->r9, r12|->r10, r12|->r11, r13|->r1, r13|->r2, r13|->r4, r13|->r5, r13|->r6, r13|->r7, r13|->r9, r13|->r12, r14|->r2, r14|->r6, r14|->r10, r14|->r12, r15|->r0, r15|->r2, r15|->r3, r15|->r5, r15|->r6, r15|->r7, r15|->r8, r15|->r9, r15|->r10, r15|->r11, r15|->r12, r15|->r13, r15|->r14, r16|->r1, r16|->r3, r16|->r5, r16|->r6, r16|->r7, r16|->r8, r16|->r10, r16|->r11, r17|->r3, r17|->r5, r17|->r6, r17|->r7, r17|->r9, r17|->r10, r17|->r12, r17|->r13, r17|->r14, r18|->r0, r18|->r4, r18|->r6, r18|->r17, r19|->r0, r19|->r1, r19|->r5, r19|->r7, r19|->r10, r19|->r11, r19|->r12, r19|->r13, r19|->r16, r20|->r0, r20|->r1, r20|->r5, r20|->r6, r20|->r7, r20|->r8, r20|->r13, r20|->r15, r20|->r16, r20|->r18, r20|->r19, r21|->r0, r21|->r1, r21|->r2, r21|->r4, r21|->r6, r21|->r7, r21|->r8, r21|->r10, r21|->r13, r21|->r14, r21|->r17, r21|->r18, r21|->r19, r21|->r20, r22|->r0, r22|->r1, r22|->r2, r22|->r4, r22|->r6, r22|->r7, r22|->r8, r22|->r9, r22|->r11, r22|->r12, r22|->r17, r22|->r18, r22|->r20, r22|->r21, r23|->r0, r23|->r3, r23|->r4, r23|->r5, r23|->r7, r23|->r8, r23|->r10, r23|->r14, r23|->r15, r23|->r17, r23|->r19, r23|->r20, r23|->r21, r24|->r0, r24|->r3, r24|->r4, r24|->r6, r24|->r10, r24|->r12, r24|->r13, r24|->r16, r24|->r18, r24|->r19, r24|->r20, r24|->r21, r24|->r23, r25|->r0, r25|->r4, r25|->r5, r25|->r14, r25|->r19, r25|->r21, r25|->r24, r26|->r3, r26|->r4, r26|->r9, r26|->r10, r26|->r11, r26|->r15, r26|->r16, r26|->r18, r26|->r20, r26|->r21, r27|->r0, r27|->r5, r27|->r6, r27|->r10, r27|->r12, r27|->r13, r27|->r17, r27|->r19, r27|->r21, r27|->r23, r27|->r24, r28|->r1, r28|->r3, r28|->r4, r28|->r5, r28|->r6, r28|->r7, r28|->r9, r28|->r10, r28|->r16, r28|->r17, r28|->r18, r28|->r22, r28|->r23, r28|->r24, r28|->r25, r28|->r26, r29|->r2, r29|->r4, r29|->r5, r29|->r7, r29|->r8, r29|->r9, r29|->r12, r29|->r13, r29|->r17, r29|->r18, r29|->r19, r29|->r21, r29|->r22, r29|->r23, r29|->r24, r29|->r27, r30|->r2, r30|->r3, r30|->r7, r30|->r9, r30|->r10, r30|->r11, r30|->r12, r30|->r13, r30|->r14, r30|->r15, r30|->r19, r30|->r25, r30|->r26, r30|->r27, r31|->r6, r31|->r8, r31|->r10, r31|->r15, r31|->r16, r31|->r18, r31|->r20, r31|->r21, r31|->r22, r31|->r24, r31|->r25, r31|->r27, r31|->r28, r31|->r30, r32|->r0, r32|->r4, r32|->r5, r32|->r6, r32|->r7, r32|->r8, r32|->r10, r32|->r14, r32|->r16, r32|->r17, r32|->r18, r32|->r22, r32|->r23, r32|->r29, r32|->r30, r32|->r31, r33|->r3, r33|->r9, r33|->r11, r33|->r12, r33|->r14, r33|->r16, r33|->r22, r33|->r23, r33|->r26, r33|->r30, r33|->r31, r33|->r32, r34|->r0, r34|->r3, r34|->r6, r34|->r7, r34|->r9, r34|->r10, r34|->r12, r34|->r16, r34|->r17, r34|->r18, r34|->r21, r34|->r24, r34|->r25, r34|->r26, r34|->r28, r34|->r30, r34|->r31, r34|->r32, r35|->r0, r35|->r1, r35|->r3, r35|->r4, r35|->r7, r35|->r8, r35|->r9, r35|->r13, r35|->r14, r35|->r18, r35|->r20, r35|->r25, r35|->r26, r35|->r27, r35|->r29, r35|->r31, r35|->r34, r36|->r1, r36|->r6, r36|->r7, r36|->r8, r36|->r10, r36|->r13, r36|->r15, r36|->r19, r36|->r22, r36|->r25, r36|->r26, r36|->r28, r36|->r31, r36|->r34, r36|->r35, r37|->r2, r37|->r3, r37|->r4, r37|->r7, r37|->r11, r37|->r13, r37|->r14, r37|->r15, r37|->r17, r37|->r19, r37|->r20, r37|->r25, r37|->r27, r37|->r28, r37|->r30, r37|->r31, r37|->r33, r37|->r35, r38|->r0, r38|->r1, r38|->r2, r38|->r4, r38|->r5, r38|->r7, r38|->r11, r38|->r12, r38|->r13, r38|->r16, r38|->r17, r38|->r24, r38|->r26, r38|->r31, r38|->r32, r38|->r34, r38|->r36, r38|->r37, r39|->r0, r39|->r7, r39|->r8, r39|->r9, r39|->r10, r39|->r12, r39|->r14, r39|->r15, r39|->r19, r39|->r26, r39|->r27, r39|->r28, r39|->r31, r39|->r34, r39|->r35, r39|->r36, r39|->r37, r39|->r38, r40|->r2, r40|->r3, r40|->r5, r40|->r7, r40|->r11, r40|->r12, r40|->r16, r40|->r17, r40|->r20, r40|->r23, r40|->r24, r40|->r25, r40|->r26, r40|->r28, r40|->r30, r40|->r32, r40|->r33, r40|->r36, r40|->r37, r41|->r0, r41|->r2, r41|->r4, r41|->r5, r41|->r8, r41|->r9, r41|->r11, r41|->r12, r41|->r13, r41|->r14, r41|->r24, r41|->r25, r41|->r28, r41|->r29, r41|->r30, r41|->r31, r41|->r32, r41|->r33, r41|->r34, r41|->r36, r41|->r37, r41|->r38, r41|->r39, r42|->r1, r42|->r6, r42|->r7, r42|->r8, r42|->r9, r42|->r10, r42|->r12, r42|->r13, r42|->r15, r42|->r17, r42|->r20, r42|->r21, r42|->r22, r42|->r23, r42|->r24, r42|->r26, r42|->r28, r42|->r29, r42|->r30, r42|->r31, r42|->r32, r42|->r34, r42|->r37, r42|->r38, r42|->r39, r42|->r40, r42|->r41, r43|->r1, r43|->r3, r43|->r5, r43|->r8, r43|->r9, r43|->r11, r43|->r12, r43|->r13, r43|->r15, r43|->r16, r43|->r20, r43|->r23, r43|->r26, r43|->r27, r43|->r28, r43|->r31, r43|->r32, r43|->r33, r43|->r34, r43|->r39, r43|->r41, r43|->r42, r44|->r3, r44|->r7, r44|->r8, r44|->r10, r44|->r12, r44|->r13, r44|->r14, r44|->r15, r44|->r21, r44|->r22, r44|->r23, r44|->r24, r44|->r29, r44|->r30, r44|->r34, r44|->r35, r44|->r36, r44|->r39, r44|->r40, r44|->r43, r45|->r9, r45|->r11, r45|->r12, r45|->r13, r45|->r17, r45|->r23, r45|->r26, r45|->r27, r45|->r29, r45|->r30, r45|->r31, r45|->r34, r45|->r38, r45|->r39, r45|->r41, r45|->r42, r46|->r0, r46|->r1, r46|->r4, r46|->r5, r46|->r8, r46|->r9, r46|->r12, r46|->r14, r46|->r15, r46|->r16, r46|->r17, r46|->r19, r46|->r21, r46|->r26, r46|->r29, r46|->r32, r46|->r37, r46|->r38, r46|->r42, r46|->r43, r46|->r45, r47|->r0, r47|->r2, r47|->r4, r47|->r8, r47|->r10, r47|->r12, r47|->r14, r47|->r15, r47|->r26, r47|->r29, r47|->r30, r47|->r31, r47|->r32, r47|->r33, r47|->r34, r47|->r35, r47|->r38, r47|->r40, r47|->r41, r47|->r44, r47|->r46, r48|->r1, r48|->r13, r48|->r14, r48|->r16, r48|->r19, r48|->r20, r48|->r21, r48|->r22, r48|->r25, r48|->r28, r48|->r29, r48|->r31, r48|->r33, r48|->r35, r48|->r36, r48|->r38, r48|->r41, r48|->r43, r48|->r44, r48|->r45, r48|->r47, r49|->r0, r49|->r1, r49|->r5, r49|->r7, r49|->r12, r49|->r15, r49|->r16, r49|->r17, r49|->r18, r49|->r20, r49|->r22, r49|->r23, r49|->r24, r49|->r25, r49|->r26, r49|->r28, r49|->r29, r49|->r30, r49|->r31, r49|->r35, r49|->r37, r49|->r42, r49|->r43, r49|->r44, r49|->r45, r49|->r46, r49|->r48, r50|->r2, r50|->r5, r50|->r6, r50|->r8, r50|->r9, r50|->r10, r50|->r12, r50|->r13, r50|->r15, r50|->r16, r50|->r17, r50|->r18, r50|->r19, r50|->r20, r50|->r21, r50|->r22, r50|->r23, r50|->r24, r50|->r29, r50|->r30, r50|->r31, r50|->r38, r50|->r40, r50|->r41, r50|->r42, r50|->r45, r50|->r46, r50|->r47, r50|->r49, r51|->r0, r51|->r3, r51|->r4, r51|->r5, r51|->r6, r51|->r7, r51|->r8, r51|->r10, r51|->r13, r51|->r15, r51|->r17, r51|->r19, r51|->r20, r51|->r22, r51|->r25, r51|->r26, r51|->r28, r51|->r30, r51|->r33, r51|->r38, r51|->r41, r51|->r42, r51|->r44, r51|->r46, r51|->r49, r51|->r50, r52|->r0, r52|->r3, r52|->r4, r52|->r5, r52|->r6, r52|->r10, r52|->r11, r52|->r17, r52|->r18, r52|->r20, r52|->r24, r52|->r26, r52|->r27, r52|->r28, r52|->r31, r52|->r32, r52|->r33, r52|->r34, r52|->r36, r52|->r38, r52|->r39, r52|->r40, r52|->r41, r52|->r42, r52|->r43, r52|->r44, r52|->r45, r52|->r48, r53|->r0, r53|->r1, r53|->r4, r53|->r6, r53|->r9, r53|->r10, r53|->r11, r53|->r15, r53|->r18, r53|->r19, r53|->r20, r53|->r21, r53|->r29, r53|->r30, r53|->r32, r53|->r33, r53|->r35, r53|->r37, r53|->r39, r53|->r44, r53|->r45, r53|->r46, r53|->r47, r53|->r48, r53|->r49, r53|->r50, r53|->r51, r54|->r0, r54|->r2, r54|->r4, r54|->r5, r54|->r7, r54|->r8, r54|->r9, r54|->r10, r54|->r11, r54|->r17, r54|->r18, r54|->r21, r54|->r26, r54|->r29, r54|->r31, r54|->r33, r54|->r35, r54|->r36, r54|->r37, r54|->r39, r54|->r40, r54|->r41, r54|->r43, r54|->r44, r54|->r45, r54|->r46, r54|->r47, r54|->r49, r54|->r50, r54|->r51, r54|->r53} &
    rules={rule0|->(rec(su:s35,re:r31,mo:pro,pr: 2,co:{c3,c9,c2,c6})), rule1|->(rec(su:s54,re:r12,mo:pro,pr: 2,co:{c6,c5,c3})), rule2|->(rec(su:s20,re:r5,mo:per,pr: 3,co:{c3,c5,c9,c2})), rule3|->(rec(su:s27,re:r50,mo:pro,pr: 1,co:{c9,c3,c6,c7})), rule4|->(rec(su:s35,re:r15,mo:pro,pr: 3,co:{c8,c4,c7,c5,c0,c9,c1})), rule5|->(rec(su:s53,re:r40,mo:per,pr: 0,co:{c0,c5,c2,c6,c7})), rule6|->(rec(su:s32,re:r24,mo:pro,pr: 2,co:{c3,c6,c2,c1,c5})), rule7|->(rec(su:s22,re:r33,mo:pro,pr: 1,co:{c3,c5,c6,c0,c9})), rule8|->(rec(su:s46,re:r1,mo:per,pr: 2,co:{c1,c7,c4,c6})), rule9|->(rec(su:s47,re:r50,mo:per,pr: 4,co:{c5,c3,c9,c8,c0,c1})), rule10|->(rec(su:s35,re:r36,mo:per,pr: 3,co:{c6})), rule11|->(rec(su:s30,re:r44,mo:pro,pr: 0,co:{c7,c4,c6,c2,c5,c1,c9})), rule12|->(rec(su:s36,re:r9,mo:pro,pr: 3,co:{c5,c0}))}

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