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
    e_sub={s1|->s0, s2|->s1, s4|->s0, s4|->s1, s4|->s2, s5|->s0, s5|->s4, s6|->s4, s6|->s5, s7|->s0, s7|->s1, s7|->s2, s7|->s3, s7|->s4, s7|->s6, s8|->s2, s8|->s5, s8|->s6, s9|->s2, s9|->s3, s9|->s4, s9|->s7, s10|->s2, s10|->s3, s10|->s9, s11|->s0, s11|->s1, s11|->s2, s11|->s5, s11|->s6, s11|->s9, s12|->s3, s12|->s4, s12|->s5, s12|->s6, s12|->s7, s12|->s8, s12|->s9, s12|->s11, s13|->s1, s13|->s3, s13|->s4, s13|->s5, s13|->s9, s13|->s10, s13|->s12, s14|->s1, s14|->s2, s14|->s5, s14|->s7, s15|->s0, s15|->s3, s15|->s4, s15|->s5, s15|->s6, s15|->s8, s15|->s9, s15|->s11, s15|->s12, s15|->s14, s16|->s0, s16|->s3, s16|->s6, s16|->s8, s16|->s9, s16|->s10, s16|->s11, s16|->s12, s16|->s13, s16|->s14, s17|->s1, s17|->s5, s17|->s7, s17|->s8, s17|->s9, s17|->s10, s17|->s12, s17|->s13, s18|->s0, s18|->s4, s18|->s5, s18|->s7, s18|->s8, s18|->s10, s18|->s11, s18|->s15, s18|->s16, s18|->s17, s19|->s4, s19|->s8, s19|->s10, s19|->s12, s19|->s13, s19|->s16, s19|->s17, s20|->s1, s20|->s3, s20|->s5, s20|->s6, s20|->s9, s20|->s12, s20|->s13, s20|->s15, s20|->s16, s20|->s19, s21|->s2, s21|->s3, s21|->s4, s21|->s7, s21|->s8, s21|->s10, s21|->s11, s21|->s12, s21|->s19, s21|->s20, s22|->s1, s22|->s2, s22|->s8, s22|->s9, s22|->s14, s22|->s15, s22|->s19, s22|->s20, s23|->s0, s23|->s1, s23|->s2, s23|->s3, s23|->s7, s23|->s12, s23|->s13, s23|->s17, s23|->s19, s23|->s20, s24|->s2, s24|->s3, s24|->s6, s24|->s8, s24|->s10, s24|->s12, s24|->s16, s24|->s17, s24|->s18, s24|->s19, s24|->s20, s25|->s0, s25|->s1, s25|->s2, s25|->s3, s25|->s4, s25|->s6, s25|->s8, s25|->s10, s25|->s12, s25|->s15, s25|->s16, s25|->s17, s25|->s18, s25|->s19, s25|->s21, s25|->s22, s25|->s23, s25|->s24, s26|->s0, s26|->s1, s26|->s2, s26|->s4, s26|->s5, s26|->s6, s26|->s8, s26|->s12, s26|->s16, s26|->s18, s26|->s20, s26|->s23, s26|->s24, s26|->s25, s27|->s0, s27|->s1, s27|->s2, s27|->s3, s27|->s7, s27|->s8, s27|->s11, s27|->s13, s27|->s16, s27|->s17, s27|->s18, s27|->s19, s27|->s20, s27|->s21, s27|->s23, s28|->s2, s28|->s8, s28|->s9, s28|->s12, s28|->s13, s28|->s14, s28|->s16, s28|->s19, s28|->s20, s28|->s22, s28|->s23, s28|->s24, s28|->s25, s28|->s27, s29|->s1, s29|->s2, s29|->s3, s29|->s4, s29|->s5, s29|->s7, s29|->s11, s29|->s12, s29|->s14, s29|->s18, s29|->s19, s29|->s20, s29|->s21, s29|->s22, s29|->s24, s29|->s25, s29|->s26, s29|->s27, s29|->s28, s30|->s0, s30|->s3, s30|->s8, s30|->s11, s30|->s12, s30|->s13, s30|->s14, s30|->s15, s30|->s21, s30|->s23, s30|->s24, s30|->s26, s30|->s27, s31|->s2, s31|->s3, s31|->s6, s31|->s7, s31|->s8, s31|->s11, s31|->s13, s31|->s14, s31|->s18, s31|->s19, s31|->s20, s31|->s23, s31|->s26, s31|->s27, s31|->s28, s32|->s1, s32|->s6, s32|->s10, s32|->s11, s32|->s14, s32|->s15, s32|->s16, s32|->s20, s32|->s22, s32|->s23, s32|->s24, s32|->s25, s32|->s28, s32|->s29, s32|->s31, s33|->s2, s33|->s3, s33|->s5, s33|->s8, s33|->s9, s33|->s10, s33|->s12, s33|->s14, s33|->s15, s33|->s16, s33|->s17, s33|->s19, s33|->s20, s33|->s23, s33|->s26, s33|->s30, s34|->s1, s34|->s5, s34|->s8, s34|->s10, s34|->s11, s34|->s13, s34|->s18, s34|->s19, s34|->s20, s34|->s23, s34|->s26, s34|->s29, s34|->s30, s34|->s32, s34|->s33, s35|->s2, s35|->s4, s35|->s5, s35|->s6, s35|->s10, s35|->s15, s35|->s17, s35|->s19, s35|->s22, s35|->s28, s35|->s30, s35|->s33, s35|->s34, s36|->s0, s36|->s1, s36|->s5, s36|->s6, s36|->s7, s36|->s8, s36|->s10, s36|->s13, s36|->s15, s36|->s19, s36|->s21, s36|->s24, s36|->s25, s36|->s27, s36|->s35, s37|->s1, s37|->s2, s37|->s3, s37|->s4, s37|->s5, s37|->s7, s37|->s8, s37|->s10, s37|->s11, s37|->s12, s37|->s13, s37|->s14, s37|->s15, s37|->s16, s37|->s17, s37|->s20, s37|->s21, s37|->s22, s37|->s25, s37|->s26, s37|->s27, s37|->s28, s37|->s29, s37|->s30, s37|->s32, s37|->s33, s37|->s34, s37|->s36, s38|->s1, s38|->s3, s38|->s7, s38|->s13, s38|->s14, s38|->s18, s38|->s22, s38|->s24, s38|->s25, s38|->s26, s38|->s27, s38|->s30, s38|->s35, s38|->s36, s38|->s37, s39|->s1, s39|->s3, s39|->s5, s39|->s6, s39|->s7, s39|->s8, s39|->s11, s39|->s14, s39|->s15, s39|->s16, s39|->s17, s39|->s20, s39|->s22, s39|->s23, s39|->s26, s39|->s27, s39|->s29, s39|->s31, s39|->s32, s39|->s33, s39|->s37, s39|->s38, s40|->s1, s40|->s4, s40|->s6, s40|->s7, s40|->s11, s40|->s13, s40|->s14, s40|->s15, s40|->s20, s40|->s21, s40|->s26, s40|->s27, s40|->s30, s40|->s31, s40|->s33, s41|->s1, s41|->s4, s41|->s5, s41|->s11, s41|->s12, s41|->s13, s41|->s18, s41|->s19, s41|->s20, s41|->s21, s41|->s23, s41|->s24, s41|->s25, s41|->s26, s41|->s27, s41|->s28, s41|->s29, s41|->s30, s41|->s33, s41|->s35, s41|->s36, s41|->s37, s42|->s0, s42|->s3, s42|->s4, s42|->s5, s42|->s6, s42|->s9, s42|->s10, s42|->s11, s42|->s16, s42|->s17, s42|->s21, s42|->s22, s42|->s23, s42|->s24, s42|->s26, s42|->s28, s42|->s31, s42|->s33, s42|->s34, s42|->s35, s42|->s36, s42|->s38, s42|->s39, s42|->s40, s42|->s41} &
    e_res={r1|->r0, r2|->r0, r3|->r0, r4|->r1, r4|->r2, r4|->r3, r5|->r0, r5|->r1, r6|->r3, r6|->r5, r7|->r3, r7|->r4, r7|->r5, r8|->r0, r8|->r1, r8|->r2, r8|->r3, r8|->r7, r9|->r1, r9|->r2, r9|->r6, r9|->r7, r9|->r8, r10|->r0, r10|->r2, r10|->r3, r10|->r4, r10|->r6, r10|->r7, r10|->r8, r10|->r9, r11|->r1, r11|->r2, r11|->r3, r11|->r6, r11|->r8, r11|->r10, r12|->r0, r12|->r1, r12|->r2, r12|->r4, r12|->r6, r12|->r7, r12|->r8, r12|->r9, r12|->r10, r12|->r11, r13|->r1, r13|->r2, r13|->r4, r13|->r5, r13|->r6, r13|->r7, r13|->r9, r14|->r2, r14|->r3, r14|->r4, r14|->r5, r14|->r7, r14|->r9, r14|->r11, r14|->r13, r15|->r3, r15|->r5, r15|->r6, r15|->r8, r15|->r11, r15|->r12, r16|->r0, r16|->r1, r16|->r2, r16|->r3, r16|->r4, r16|->r5, r16|->r8, r16|->r13, r16|->r14, r17|->r1, r17|->r2, r17|->r6, r17|->r8, r17|->r10, r17|->r16, r18|->r0, r18|->r1, r18|->r2, r18|->r4, r18|->r7, r18|->r8, r18|->r10, r18|->r11, r18|->r13, r18|->r14, r18|->r17, r19|->r0, r19|->r3, r19|->r4, r19|->r6, r19|->r7, r19|->r9, r19|->r12, r19|->r13, r19|->r14, r19|->r15, r20|->r0, r20|->r2, r20|->r5, r20|->r6, r20|->r7, r20|->r8, r20|->r9, r20|->r11, r20|->r13, r20|->r14, r20|->r15, r20|->r18, r21|->r0, r21|->r1, r21|->r6, r21|->r7, r21|->r8, r21|->r12, r21|->r14, r21|->r18, r21|->r19, r22|->r2, r22|->r3, r22|->r4, r22|->r10, r22|->r13, r22|->r14, r22|->r17, r22|->r20, r22|->r21, r23|->r0, r23|->r2, r23|->r6, r23|->r7, r23|->r8, r23|->r10, r23|->r14, r23|->r15, r23|->r16, r23|->r17, r23|->r19, r23|->r20, r23|->r22, r24|->r4, r24|->r5, r24|->r6, r24|->r7, r24|->r8, r24|->r10, r24|->r11, r24|->r13, r24|->r14, r24|->r16, r24|->r17, r24|->r18, r24|->r19, r24|->r21, r24|->r23, r25|->r0, r25|->r1, r25|->r2, r25|->r3, r25|->r7, r25|->r8, r25|->r12, r25|->r13, r25|->r15, r25|->r16, r25|->r17, r25|->r19, r25|->r23, r25|->r24, r26|->r1, r26|->r2, r26|->r4, r26|->r6, r26|->r7, r26|->r10, r26|->r12, r26|->r14, r26|->r15, r26|->r17, r26|->r18, r26|->r19, r26|->r21, r26|->r23, r27|->r0, r27|->r1, r27|->r3, r27|->r4, r27|->r6, r27|->r7, r27|->r9, r27|->r11, r27|->r12, r27|->r14, r27|->r15, r27|->r19, r27|->r20, r27|->r21, r27|->r24, r27|->r26, r28|->r1, r28|->r2, r28|->r3, r28|->r4, r28|->r5, r28|->r6, r28|->r7, r28|->r8, r28|->r10, r28|->r13, r28|->r17, r28|->r18, r28|->r19, r28|->r20, r28|->r26, r28|->r27, r29|->r1, r29|->r3, r29|->r4, r29|->r5, r29|->r8, r29|->r9, r29|->r10, r29|->r11, r29|->r13, r29|->r15, r29|->r16, r29|->r17, r29|->r18, r29|->r19, r29|->r20, r29|->r23, r29|->r25, r29|->r28, r30|->r0, r30|->r1, r30|->r3, r30|->r5, r30|->r6, r30|->r7, r30|->r11, r30|->r12, r30|->r14, r30|->r20, r30|->r23, r30|->r29, r31|->r2, r31|->r4, r31|->r8, r31|->r9, r31|->r10, r31|->r12, r31|->r14, r31|->r15, r31|->r16, r31|->r19, r31|->r20, r31|->r22, r31|->r24, r31|->r28, r31|->r29, r31|->r30, r32|->r1, r32|->r6, r32|->r14, r32|->r18, r32|->r20, r32|->r21, r32|->r22, r32|->r23, r32|->r26, r32|->r30, r32|->r31, r33|->r0, r33|->r3, r33|->r5, r33|->r11, r33|->r14, r33|->r15, r33|->r16, r33|->r18, r33|->r20, r33|->r22, r33|->r23, r33|->r25, r33|->r28, r33|->r29, r33|->r30, r33|->r31, r34|->r7, r34|->r9, r34|->r10, r34|->r17, r34|->r18, r34|->r19, r34|->r20, r34|->r21, r34|->r22, r34|->r24, r34|->r30, r34|->r31, r34|->r33, r35|->r0, r35|->r1, r35|->r2, r35|->r3, r35|->r4, r35|->r6, r35|->r7, r35|->r9, r35|->r13, r35|->r15, r35|->r17, r35|->r18, r35|->r23, r35|->r25, r35|->r26, r35|->r27, r35|->r28, r35|->r30, r35|->r31, r35|->r32, r35|->r33, r36|->r0, r36|->r4, r36|->r5, r36|->r12, r36|->r15, r36|->r20, r36|->r22, r36|->r23, r36|->r24, r36|->r30, r36|->r31, r36|->r33, r37|->r0, r37|->r1, r37|->r3, r37|->r4, r37|->r5, r37|->r7, r37|->r9, r37|->r11, r37|->r14, r37|->r15, r37|->r20, r37|->r21, r37|->r23, r37|->r26, r37|->r27, r37|->r32, r37|->r34, r37|->r35, r38|->r0, r38|->r2, r38|->r4, r38|->r7, r38|->r8, r38|->r11, r38|->r12, r38|->r15, r38|->r16, r38|->r18, r38|->r20, r38|->r24, r38|->r26, r38|->r31, r38|->r32, r38|->r35, r38|->r37, r39|->r3, r39|->r4, r39|->r6, r39|->r11, r39|->r14, r39|->r18, r39|->r19, r39|->r22, r39|->r24, r39|->r25, r39|->r26, r39|->r29, r39|->r30, r39|->r31, r39|->r32, r39|->r33, r39|->r36, r39|->r38, r40|->r2, r40|->r3, r40|->r5, r40|->r6, r40|->r7, r40|->r8, r40|->r9, r40|->r10, r40|->r12, r40|->r13, r40|->r14, r40|->r15, r40|->r18, r40|->r20, r40|->r21, r40|->r23, r40|->r24, r40|->r25, r40|->r26, r40|->r27, r40|->r30, r40|->r35, r40|->r37, r40|->r38, r41|->r2, r41|->r3, r41|->r4, r41|->r5, r41|->r6, r41|->r7, r41|->r10, r41|->r11, r41|->r14, r41|->r15, r41|->r16, r41|->r19, r41|->r25, r41|->r26, r41|->r29, r41|->r32, r41|->r33, r41|->r34, r41|->r36, r41|->r38, r41|->r39} &
    rules={rule0|->(rec(su:s35,re:r30,mo:pro,pr: 0,co:{c9,c6,c2,c4,c0,c7})), rule1|->(rec(su:s34,re:r19,mo:pro,pr: 2,co:{c0,c9,c8,c4,c3,c1})), rule2|->(rec(su:s40,re:r38,mo:pro,pr: 4,co:{c5,c8,c7})), rule3|->(rec(su:s23,re:r31,mo:per,pr: 2,co:{c3,c8,c9,c7,c2,c1})), rule4|->(rec(su:s36,re:r36,mo:per,pr: 4,co:{c0,c1,c4,c3,c5})), rule5|->(rec(su:s37,re:r0,mo:pro,pr: 1,co:{c3,c7,c5,c4,c2,c0})), rule6|->(rec(su:s17,re:r3,mo:per,pr: 1,co:{c3,c8,c6,c5})), rule7|->(rec(su:s40,re:r40,mo:per,pr: 4,co:{c3,c1,c8})), rule8|->(rec(su:s20,re:r41,mo:pro,pr: 2,co:{c0,c1,c2})), rule9|->(rec(su:s42,re:r14,mo:pro,pr: 2,co:{c3,c1,c7})), rule10|->(rec(su:s18,re:r33,mo:per,pr: 4,co:{c9,c6,c4})), rule11|->(rec(su:s23,re:r6,mo:per,pr: 0,co:{c0,c1,c2})), rule12|->(rec(su:s15,re:r4,mo:per,pr: 4,co:{c3}))}

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