module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s1+
         s4->s3+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s5+
         s7->s1+
         s7->s4+
         s8->s2+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s3+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s7+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s11+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s12+
         s17->s3+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s14+
         s18->s16+
         s19->s1+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s11+
         s19->s12+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s7+
         s20->s9+
         s20->s12+
         s20->s14+
         s20->s16+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s16+
         s21->s17+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s17+
         s23->s19+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s7+
         s24->s9+
         s24->s11+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s22+
         s25->s23+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s16+
         s26->s18+
         s26->s20+
         s26->s21+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s7+
         s27->s8+
         s27->s13+
         s27->s14+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s18+
         s28->s22+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r6->r0+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r2+
         r7->r5+
         r8->r0+
         r9->r1+
         r9->r3+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r9+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r8+
         r13->r10+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r3+
         r15->r4+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r0+
         r16->r4+
         r16->r6+
         r16->r10+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r6+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r17+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r12+
         r19->r16+
         r20->r0+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r17+
         r20->r19+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r10+
         r21->r12+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r12+
         r22->r14+
         r22->r17+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r9+
         r23->r11+
         r23->r15+
         r23->r17+
         r23->r18+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r4+
         r24->r6+
         r24->r8+
         r24->r9+
         r24->r13+
         r24->r15+
         r24->r18+
         r24->r19+
         r24->r20+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r6+
         r25->r7+
         r25->r11+
         r25->r14+
         r25->r16+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r5+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r21+
         r26->r23+
         r26->r24+
         r27->r0+
         r27->r2+
         r27->r5+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r25+
         r28->r0+
         r28->r2+
         r28->r3+
         r28->r5+
         r28->r7+
         r28->r8+
         r28->r11+
         r28->r12+
         r28->r15+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r9+
         r29->r10+
         r29->r16+
         r29->r17+
         r29->r20+
         r29->r26+
         r29->r28}

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
    s =s2
    t =r27
    m = permission
    p = 0
    c = c0+c1
}
one sig rule1 extends Rule{}{
    s =s20
    t =r0
    m = prohibition
    p = 4
    c = c9+c4+c8
}
one sig rule2 extends Rule{}{
    s =s20
    t =r8
    m = prohibition
    p = 0
    c = c1+c6+c4+c7+c9
}
one sig rule3 extends Rule{}{
    s =s23
    t =r14
    m = permission
    p = 3
    c = c5+c6+c3+c2+c9
}
one sig rule4 extends Rule{}{
    s =s0
    t =r11
    m = prohibition
    p = 4
    c = c4+c6+c7+c5+c3+c8+c2
}
one sig rule5 extends Rule{}{
    s =s0
    t =r11
    m = prohibition
    p = 3
    c = c9+c0+c7+c3+c1
}
one sig rule6 extends Rule{}{
    s =s24
    t =r13
    m = prohibition
    p = 3
    c = c4+c1+c3+c9+c0+c2
}
one sig rule7 extends Rule{}{
    s =s17
    t =r0
    m = permission
    p = 4
    c = c4+c6+c3+c0
}
one sig rule8 extends Rule{}{
    s =s7
    t =r6
    m = prohibition
    p = 4
    c = c8+c2+c5+c6+c7+c1+c0
}
one sig rule9 extends Rule{}{
    s =s21
    t =r26
    m = permission
    p = 0
    c = c1+c0+c6+c7+c5
}
one sig rule10 extends Rule{}{
    s =s13
    t =r29
    m = permission
    p = 2
    c = c9+c5+c2
}
one sig rule11 extends Rule{}{
    s =s4
    t =r24
    m = prohibition
    p = 0
    c = c1
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

