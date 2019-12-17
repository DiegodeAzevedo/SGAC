module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s1+
         s7->s1+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s7+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s14+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s11+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s17+
         s21->s0+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s18+
         s22->s19+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s10+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s20+
         s23->s22+
         s24->s1+
         s24->s3+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s12+
         s25->s15+
         s25->s20+
         s25->s21+
         s25->s22+
         s26->s0+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s6+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s23+
         s27->s3+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s13+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s20+
         s28->s0+
         s28->s2+
         s28->s5+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s23+
         s28->s26+
         s28->s27+
         s29->s1+
         s29->s4+
         s29->s5+
         s29->s10+
         s29->s12+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s20+
         s29->s24+
         s29->s25+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r4->r3+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r2+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r7+
         r10->r0+
         r10->r6+
         r11->r2+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r9+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r13+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r17+
         r20->r19+
         r21->r0+
         r21->r3+
         r21->r6+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r17+
         r21->r19+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r11+
         r22->r14+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r16+
         r23->r17+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r22+
         r25->r0+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r9+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r17+
         r26->r19+
         r26->r20+
         r27->r0+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r14+
         r27->r15+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r28->r1+
         r28->r2+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r18+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r10+
         r29->r11+
         r29->r15+
         r29->r18+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r25+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s28
    t =r27
    m = permission
    p = 4
    c = c12+c0+c14+c1+c18+c16+c10
}
one sig rule1 extends Rule{}{
    s =s21
    t =r20
    m = prohibition
    p = 3
    c = c12+c13+c1+c14+c19+c6+c0+c9
}
one sig rule2 extends Rule{}{
    s =s3
    t =r24
    m = prohibition
    p = 3
    c = c10+c7+c1+c11+c3+c2+c5+c13+c8+c18+c6+c19
}
one sig rule3 extends Rule{}{
    s =s5
    t =r28
    m = permission
    p = 4
    c = c2+c8+c3+c5+c7+c12+c1+c15
}
one sig rule4 extends Rule{}{
    s =s0
    t =r11
    m = permission
    p = 3
    c = c15+c14+c17+c0
}
one sig rule5 extends Rule{}{
    s =s25
    t =r18
    m = prohibition
    p = 4
    c = c17+c13+c6+c14+c5+c8+c11+c0
}
one sig rule6 extends Rule{}{
    s =s24
    t =r4
    m = prohibition
    p = 0
    c = c17+c19+c3+c13+c1
}
one sig rule7 extends Rule{}{
    s =s15
    t =r25
    m = permission
    p = 0
    c = c1+c13+c0+c10+c15+c16+c8+c4+c3+c17+c9+c19
}
one sig rule8 extends Rule{}{
    s =s8
    t =r15
    m = prohibition
    p = 4
    c = c17+c13+c15
}
one sig rule9 extends Rule{}{
    s =s21
    t =r13
    m = prohibition
    p = 2
    c = c17+c10+c6+c16+c15+c0+c12+c18
}
one sig rule10 extends Rule{}{
    s =s28
    t =r23
    m = permission
    p = 2
    c = c18+c3+c17+c2+c8+c6+c5+c10+c11+c19+c4
}
one sig rule11 extends Rule{}{
    s =s12
    t =r18
    m = permission
    p = 3
    c = c1+c0+c6+c16+c11+c12
}
//**************************
//***Auxiliary Predicates***
//**************************
pred access_condition[req:Request,con:Context]{
    (no  r:applicableRules[req] |  (evalRuleCond[r,con] and r.m=prohibition and
        all rule: r.^(req.ruleSucc) | not evalRuleCond[rule,con])	)
    and some { r:applicableRules[req] |evalRuleCond[r,con]}
}

//***************************
//***Determination of the ***
//***  ineffective rules  ***
//***************************

fun pseudosinkRule[req: Request, cx:Context] : set Rule{
    {r : applicableRules[req] |
        evalRuleCond[r,cx] and no ru : applicableRules[req] |
            ru in r.^(req.ruleSucc) and evalRuleCond[ru,cx]}
    }

pred ineffectiveRule[r:Rule]{
    no rq : Request | (
        r in applicableRules[rq] and some cr : r.c | (
            r in pseudosinkRule[rq,cr]
            and
            (no ru : pseudosinkRule[rq,cr]-r |
                r.m = ru.m)
            and
            (r.m = permission implies no (pseudosinkRule[rq,cr]-r))
        )
    )
}
//*** determination of unusable rules command ***

check ineffectiveRulerule0{ ineffectiveRule[rule0]}for 4

check ineffectiveRulerule1{ ineffectiveRule[rule1]}for 4

check ineffectiveRulerule2{ ineffectiveRule[rule2]}for 4

check ineffectiveRulerule3{ ineffectiveRule[rule3]}for 4

check ineffectiveRulerule4{ ineffectiveRule[rule4]}for 4

check ineffectiveRulerule5{ ineffectiveRule[rule5]}for 4

check ineffectiveRulerule6{ ineffectiveRule[rule6]}for 4

check ineffectiveRulerule7{ ineffectiveRule[rule7]}for 4

check ineffectiveRulerule8{ ineffectiveRule[rule8]}for 4

check ineffectiveRulerule9{ ineffectiveRule[rule9]}for 4

check ineffectiveRulerule10{ ineffectiveRule[rule10]}for 4

check ineffectiveRulerule11{ ineffectiveRule[rule11]}for 4

