module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s4->s2+
         s4->s3+
         s5->s1+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s9+
         s12->s1+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s6+
         s13->s7+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s12+
         s16->s1+
         s16->s4+
         s16->s6+
         s16->s10+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s4+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s15+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s12+
         s20->s15+
         s20->s17+
         s21->s0+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s15+
         s21->s17+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s21+
         s23->s2+
         s23->s5+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s14+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s1+
         s24->s2+
         s24->s4+
         s24->s5+
         s24->s12+
         s24->s13+
         s24->s17+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s13+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s22+
         s26->s24+
         s27->s0+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s5+
         s28->s7+
         s28->s9+
         s28->s14+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s5+
         s29->s6+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s24+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r3+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r5+
         r13->r7+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r8+
         r15->r11+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r7+
         r19->r10+
         r19->r14+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r3+
         r20->r4+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r16+
         r20->r17+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r14+
         r21->r17+
         r21->r19+
         r22->r2+
         r22->r3+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r19+
         r23->r0+
         r23->r1+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r12+
         r23->r18+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r5+
         r24->r6+
         r24->r10+
         r24->r13+
         r24->r16+
         r24->r18+
         r24->r19+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r4+
         r25->r8+
         r25->r12+
         r25->r17+
         r25->r19+
         r25->r22+
         r25->r24+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r11+
         r26->r13+
         r26->r15+
         r26->r17+
         r26->r21+
         r26->r22+
         r26->r23+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r8+
         r27->r10+
         r27->r13+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r28->r2+
         r28->r3+
         r28->r6+
         r28->r8+
         r28->r17+
         r28->r23+
         r28->r24+
         r28->r27+
         r29->r2+
         r29->r3+
         r29->r9+
         r29->r11+
         r29->r15+
         r29->r16+
         r29->r20+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r27}

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
    s =s19
    t =r5
    m = permission
    p = 4
    c = c1+c5+c9
}
one sig rule1 extends Rule{}{
    s =s16
    t =r20
    m = permission
    p = 4
    c = c6+c7+c1+c0+c4
}
one sig rule2 extends Rule{}{
    s =s6
    t =r21
    m = permission
    p = 0
    c = c3+c2+c5+c4+c9+c7+c1+c6
}
one sig rule3 extends Rule{}{
    s =s15
    t =r8
    m = prohibition
    p = 0
    c = c0+c5+c9+c4+c3+c6
}
one sig rule4 extends Rule{}{
    s =s9
    t =r28
    m = permission
    p = 3
    c = c0+c2+c5+c9+c1+c4
}
one sig rule5 extends Rule{}{
    s =s1
    t =r22
    m = permission
    p = 3
    c = c9+c7+c8+c6
}
one sig rule6 extends Rule{}{
    s =s5
    t =r11
    m = prohibition
    p = 2
    c = c7+c9+c6+c3+c2+c4+c0
}
one sig rule7 extends Rule{}{
    s =s16
    t =r8
    m = prohibition
    p = 1
    c = c6+c3+c8+c4+c7
}
one sig rule8 extends Rule{}{
    s =s16
    t =r27
    m = permission
    p = 1
    c = c3+c5+c1+c0+c9+c6+c7
}
one sig rule9 extends Rule{}{
    s =s25
    t =r14
    m = prohibition
    p = 2
    c = c8+c5
}
one sig rule10 extends Rule{}{
    s =s4
    t =r15
    m = prohibition
    p = 2
    c = c5+c7+c0
}
one sig rule11 extends Rule{}{
    s =s19
    t =r14
    m = permission
    p = 4
    c = c9+c0+c5
}
one sig rule12 extends Rule{}{
    s =s14
    t =r1
    m = prohibition
    p = 3
    c = c2+c0+c1
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

