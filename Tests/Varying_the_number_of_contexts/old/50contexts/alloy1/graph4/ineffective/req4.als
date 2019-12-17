module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s1+
         s4->s1+
         s4->s2+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s5+
         s7->s6+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s6+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s12+
         s14->s1+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s14+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s5+
         s21->s7+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s19+
         s22->s2+
         s22->s3+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s18+
         s22->s21+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s21+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s14+
         s24->s16+
         s24->s18+
         s24->s22+
         s24->s23+
         s25->s1+
         s25->s3+
         s25->s6+
         s25->s12+
         s25->s13+
         s25->s15+
         s25->s19+
         s25->s23+
         s26->s0+
         s26->s1+
         s26->s4+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s13+
         s26->s14+
         s26->s17+
         s26->s19+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s18+
         s27->s20+
         s27->s22+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s24+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s22+
         s29->s23+
         s29->s25+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r3+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r7+
         r11->r9+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r3+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r12+
         r17->r14+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r17+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r2+
         r21->r3+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r18+
         r23->r0+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r22+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r18+
         r24->r19+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r5+
         r25->r7+
         r25->r8+
         r25->r11+
         r25->r14+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r22+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r15+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r23+
         r27->r24+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r7+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r23+
         r28->r25+
         r28->r26+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r16+
         r29->r17+
         r29->r20+
         r29->r21+
         r29->r23+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r24
    m = prohibition
    p = 0
    c = c3+c9+c7+c6+c1
}
one sig rule1 extends Rule{}{
    s =s22
    t =r22
    m = prohibition
    p = 1
    c = c3+c8+c9+c6+c0+c5+c7+c2
}
one sig rule2 extends Rule{}{
    s =s24
    t =r12
    m = permission
    p = 1
    c = c1+c7+c6+c3+c2+c9+c5+c0
}
one sig rule3 extends Rule{}{
    s =s12
    t =r29
    m = permission
    p = 3
    c = c2+c0+c8+c1+c3
}
one sig rule4 extends Rule{}{
    s =s14
    t =r14
    m = permission
    p = 4
    c = c2+c3+c9+c8+c1+c4+c6
}
one sig rule5 extends Rule{}{
    s =s2
    t =r14
    m = permission
    p = 1
    c = c4
}
one sig rule6 extends Rule{}{
    s =s0
    t =r24
    m = prohibition
    p = 0
    c = c5+c1+c8+c3+c0+c9
}
one sig rule7 extends Rule{}{
    s =s5
    t =r9
    m = prohibition
    p = 0
    c = c5+c6+c3+c2+c7+c8
}
one sig rule8 extends Rule{}{
    s =s11
    t =r10
    m = permission
    p = 0
    c = c0+c6+c3+c8
}
one sig rule9 extends Rule{}{
    s =s15
    t =r20
    m = permission
    p = 1
    c = c4+c6+c7+c0
}
one sig rule10 extends Rule{}{
    s =s13
    t =r8
    m = permission
    p = 0
    c = c6+c7+c5+c9+c4+c8+c1
}
one sig rule11 extends Rule{}{
    s =s17
    t =r4
    m = prohibition
    p = 4
    c = c4+c6+c0+c2+c5+c9+c1
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

