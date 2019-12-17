module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s5+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s1+
         s15->s3+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s12+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s14+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s17+
         s19->s18+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s9+
         s20->s10+
         s20->s13+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s9+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s16+
         s22->s17+
         s22->s19+
         s22->s20+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s14+
         s23->s17+
         s23->s18+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s16+
         s24->s19+
         s24->s20+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s5+
         s25->s8+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s22+
         s25->s23+
         s26->s0+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s9+
         s26->s14+
         s26->s16+
         s26->s18+
         s26->s19+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s6+
         s27->s9+
         s27->s11+
         s27->s12+
         s27->s15+
         s27->s16+
         s27->s18+
         s27->s21+
         s27->s23+
         s27->s26+
         s28->s1+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s19+
         s28->s23+
         s28->s26+
         s29->s3+
         s29->s4+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s12+
         s29->s14+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r4->r1+
         r4->r3+
         r5->r2+
         r5->r4+
         r6->r1+
         r6->r3+
         r7->r1+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r5+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r6+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r7+
         r15->r8+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r2+
         r16->r12+
         r16->r14+
         r17->r4+
         r17->r11+
         r17->r12+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r16+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r7+
         r20->r8+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r6+
         r21->r9+
         r21->r12+
         r21->r13+
         r21->r17+
         r21->r19+
         r22->r1+
         r22->r2+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r1+
         r23->r4+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r20+
         r24->r21+
         r24->r22+
         r25->r0+
         r25->r3+
         r25->r5+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r21+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r2+
         r26->r5+
         r26->r9+
         r26->r11+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r25+
         r27->r2+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r17+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r13+
         r28->r15+
         r28->r17+
         r28->r19+
         r28->r21+
         r28->r22+
         r28->r24+
         r29->r0+
         r29->r2+
         r29->r5+
         r29->r8+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r19+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r25+
         r29->r26}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r26
    m = permission
    p = 1
    c = c6+c3+c8
}
one sig rule1 extends Rule{}{
    s =s3
    t =r23
    m = permission
    p = 2
    c = c7
}
one sig rule2 extends Rule{}{
    s =s21
    t =r23
    m = prohibition
    p = 0
    c = c6+c3+c7
}
one sig rule3 extends Rule{}{
    s =s28
    t =r6
    m = permission
    p = 4
    c = c0+c3+c6+c1
}
one sig rule4 extends Rule{}{
    s =s13
    t =r8
    m = permission
    p = 3
    c = c8+c6+c5+c7+c4+c3+c0+c2
}
one sig rule5 extends Rule{}{
    s =s0
    t =r26
    m = permission
    p = 3
    c = c8+c3+c6+c1+c7
}
one sig rule6 extends Rule{}{
    s =s14
    t =r17
    m = permission
    p = 2
    c = c9+c0+c4+c1+c3
}
one sig rule7 extends Rule{}{
    s =s8
    t =r24
    m = prohibition
    p = 4
    c = c1+c9+c4+c8
}
one sig rule8 extends Rule{}{
    s =s27
    t =r17
    m = prohibition
    p = 2
    c = c7+c0+c6+c2+c3
}
one sig rule9 extends Rule{}{
    s =s29
    t =r29
    m = permission
    p = 1
    c = c0+c2+c7+c9+c8
}
one sig rule10 extends Rule{}{
    s =s10
    t =r27
    m = prohibition
    p = 0
    c = c0+c2+c4
}
one sig rule11 extends Rule{}{
    s =s19
    t =r20
    m = permission
    p = 4
    c = c8
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

