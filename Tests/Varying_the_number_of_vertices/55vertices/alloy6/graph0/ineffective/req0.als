module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s2+
         s4->s3+
         s5->s4+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s3+
         s7->s6+
         s8->s3+
         s8->s7+
         s9->s1+
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
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s5+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s3+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s3+
         s15->s5+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s3+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s12+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s13+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s8+
         s20->s10+
         s20->s12+
         s20->s14+
         s20->s15+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s8+
         s21->s14+
         s21->s18+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s13+
         s22->s16+
         s22->s21+
         s23->s3+
         s23->s5+
         s23->s7+
         s23->s8+
         s23->s11+
         s23->s12+
         s23->s14+
         s23->s18+
         s23->s20+
         s24->s0+
         s24->s3+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s21+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s11+
         s25->s15+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s9+
         s26->s11+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s18+
         s26->s20+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s3+
         s27->s5+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s11+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r10->r1+
         r10->r5+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r3+
         r13->r7+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r14+
         r16->r2+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r11+
         r18->r15+
         r19->r0+
         r19->r1+
         r19->r6+
         r19->r8+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r8+
         r20->r9+
         r20->r13+
         r20->r16+
         r20->r17+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r14+
         r21->r16+
         r21->r19+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r11+
         r22->r12+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r21+
         r23->r2+
         r23->r4+
         r23->r8+
         r23->r10+
         r23->r15+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r9+
         r25->r14+
         r25->r15+
         r25->r19+
         r25->r20+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r3+
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r15+
         r26->r18+
         r26->r21}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

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
    s =s1
    t =r12
    m = permission
    p = 4
    c = c4+c7+c3
}
one sig rule1 extends Rule{}{
    s =s18
    t =r23
    m = permission
    p = 1
    c = c1+c8+c9+c0
}
one sig rule2 extends Rule{}{
    s =s23
    t =r22
    m = permission
    p = 1
    c = c3+c2+c9
}
one sig rule3 extends Rule{}{
    s =s8
    t =r2
    m = prohibition
    p = 3
    c = c3+c6+c5+c2+c9+c1+c7+c0
}
one sig rule4 extends Rule{}{
    s =s23
    t =r25
    m = prohibition
    p = 1
    c = c4
}
one sig rule5 extends Rule{}{
    s =s11
    t =r9
    m = permission
    p = 0
    c = c7+c6+c1+c8+c3+c2
}
one sig rule6 extends Rule{}{
    s =s17
    t =r20
    m = permission
    p = 2
    c = c1+c0+c6
}
one sig rule7 extends Rule{}{
    s =s8
    t =r10
    m = permission
    p = 0
    c = c6+c1+c2
}
one sig rule8 extends Rule{}{
    s =s2
    t =r13
    m = prohibition
    p = 2
    c = c0+c2+c3+c9+c7+c8+c6
}
one sig rule9 extends Rule{}{
    s =s19
    t =r5
    m = permission
    p = 2
    c = c6+c0
}
one sig rule10 extends Rule{}{
    s =s17
    t =r16
    m = permission
    p = 3
    c = c7+c0+c1
}
one sig rule11 extends Rule{}{
    s =s8
    t =r15
    m = prohibition
    p = 1
    c = c3+c2+c9+c5+c4
}
one sig rule12 extends Rule{}{
    s =s24
    t =r3
    m = permission
    p = 3
    c = c4
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

check ineffectiveRulerule12{ ineffectiveRule[rule12]}for 4

