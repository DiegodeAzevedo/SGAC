module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s1+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s12->s1+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s2+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s3+
         s15->s9+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s4+
         s17->s11+
         s17->s12+
         s17->s15+
         s18->s1+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s5+
         s19->s7+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s11+
         s20->s13+
         s20->s14+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s4+
         s21->s6+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s15+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s14+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s6+
         s25->s11+
         s25->s12+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s4+
         s26->s5+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s2+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s14+
         s27->s20+
         s27->s23+
         s27->s24+
         s28->s1+
         s28->s2+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s21+
         s28->s24+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s12+
         s29->s14+
         s29->s17+
         s29->s20+
         s29->s23+
         s29->s24+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r6+
         r8->r0+
         r8->r7+
         r9->r2+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r7+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r8+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r11+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r15+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r16+
         r19->r1+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r3+
         r20->r7+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r16+
         r21->r0+
         r21->r2+
         r21->r7+
         r21->r8+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r16+
         r22->r3+
         r22->r9+
         r22->r10+
         r22->r14+
         r22->r17+
         r22->r19+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r4+
         r23->r6+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r7+
         r25->r11+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r22+
         r25->r23+
         r26->r1+
         r26->r2+
         r26->r5+
         r26->r6+
         r26->r9+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r6+
         r27->r10+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r24+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r15+
         r28->r18+
         r28->r19+
         r28->r23+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r4+
         r29->r12+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r20+
         r29->r22+
         r29->r25+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r16
    m = permission
    p = 1
    c = c7+c6+c2+c1+c5+c3
}
one sig rule1 extends Rule{}{
    s =s20
    t =r26
    m = prohibition
    p = 0
    c = c3+c8+c0
}
one sig rule2 extends Rule{}{
    s =s14
    t =r23
    m = permission
    p = 0
    c = c1
}
one sig rule3 extends Rule{}{
    s =s5
    t =r10
    m = permission
    p = 2
    c = c1+c4+c2+c6+c8+c3
}
one sig rule4 extends Rule{}{
    s =s22
    t =r12
    m = permission
    p = 4
    c = c2+c1+c9+c7+c4
}
one sig rule5 extends Rule{}{
    s =s8
    t =r4
    m = prohibition
    p = 0
    c = c0+c3+c4+c6+c8+c9+c1
}
one sig rule6 extends Rule{}{
    s =s9
    t =r13
    m = permission
    p = 1
    c = c2+c1+c5
}
one sig rule7 extends Rule{}{
    s =s20
    t =r12
    m = permission
    p = 0
    c = c7+c6+c8+c3
}
one sig rule8 extends Rule{}{
    s =s17
    t =r4
    m = permission
    p = 2
    c = c1+c4+c9+c5+c7+c3
}
one sig rule9 extends Rule{}{
    s =s6
    t =r9
    m = permission
    p = 0
    c = c4+c8+c3+c6
}
one sig rule10 extends Rule{}{
    s =s28
    t =r16
    m = prohibition
    p = 0
    c = c0+c3+c2
}
one sig rule11 extends Rule{}{
    s =s11
    t =r4
    m = permission
    p = 3
    c = c0+c1+c3+c5+c4+c2
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

