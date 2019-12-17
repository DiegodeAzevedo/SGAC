module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s1+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s7->s1+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s6+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s5+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s10+
         s12->s11+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s0+
         s16->s5+
         s16->s11+
         s17->s0+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s14+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s17+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s12+
         s21->s14+
         s21->s15+
         s21->s17+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s21+
         s23->s0+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s20+
         s23->s21+
         s24->s0+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s22+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s26->s2+
         s26->s3+
         s26->s6+
         s26->s10+
         s26->s13+
         s26->s19+
         s26->s20+
         s26->s22+
         s26->s23+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s21+
         s27->s22+
         s27->s25+
         s27->s26+
         s28->s2+
         s28->s3+
         s28->s6+
         s28->s7+
         s28->s10+
         s28->s12+
         s28->s14+
         s28->s16+
         s28->s18+
         s28->s21+
         s28->s24+
         s28->s27+
         s29->s1+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s7+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r5+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r5+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r9+
         r15->r5+
         r15->r7+
         r15->r10+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r14+
         r18->r4+
         r18->r5+
         r18->r12+
         r18->r13+
         r18->r14+
         r19->r2+
         r19->r4+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r10+
         r20->r11+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r17+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r14+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r1+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r12+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r7+
         r23->r9+
         r23->r12+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r10+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r10+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r5+
         r26->r9+
         r26->r12+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r21+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r14+
         r27->r15+
         r27->r18+
         r27->r21+
         r27->r24+
         r28->r0+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r8+
         r28->r9+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r25+
         r28->r26+
         r29->r3+
         r29->r4+
         r29->r6+
         r29->r7+
         r29->r9+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s19
    t =r1
    m = prohibition
    p = 2
    c = c1+c4+c7
}
one sig rule1 extends Rule{}{
    s =s18
    t =r10
    m = permission
    p = 1
    c = c3+c7
}
one sig rule2 extends Rule{}{
    s =s8
    t =r16
    m = permission
    p = 2
    c = c6+c7+c3
}
one sig rule3 extends Rule{}{
    s =s12
    t =r17
    m = permission
    p = 1
    c = c9+c1+c3+c0+c5+c6
}
one sig rule4 extends Rule{}{
    s =s18
    t =r26
    m = prohibition
    p = 2
    c = c1+c5+c2+c0+c6+c9
}
one sig rule5 extends Rule{}{
    s =s18
    t =r22
    m = prohibition
    p = 4
    c = c8+c0+c7+c2+c5
}
one sig rule6 extends Rule{}{
    s =s25
    t =r29
    m = permission
    p = 1
    c = c2+c9+c4
}
one sig rule7 extends Rule{}{
    s =s0
    t =r22
    m = permission
    p = 1
    c = c0+c9+c7
}
one sig rule8 extends Rule{}{
    s =s13
    t =r3
    m = permission
    p = 2
    c = c0+c1+c8+c3+c9
}
one sig rule9 extends Rule{}{
    s =s12
    t =r4
    m = permission
    p = 1
    c = c1+c6+c8
}
one sig rule10 extends Rule{}{
    s =s17
    t =r19
    m = prohibition
    p = 0
    c = c4+c1+c9+c3+c6
}
one sig rule11 extends Rule{}{
    s =s11
    t =r8
    m = prohibition
    p = 0
    c = c2+c0+c3
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

