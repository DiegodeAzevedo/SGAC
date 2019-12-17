module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s4->s2+
         s4->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s4+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s1+
         s12->s3+
         s12->s6+
         s12->s8+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s5+
         s18->s6+
         s18->s11+
         s18->s12+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s8+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s18+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s19+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s13+
         s23->s14+
         s23->s18+
         s23->s19+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s17+
         s24->s18+
         s24->s20+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s16+
         s25->s20+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s4+
         s26->s8+
         s26->s9+
         s26->s12+
         s26->s14+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s6+
         s27->s9+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s23+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s5+
         s28->s6+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s4+
         s29->s5+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r3+
         r9->r5+
         r10->r1+
         r10->r2+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r6+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r8+
         r14->r10+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r11+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r10+
         r16->r11+
         r16->r12+
         r17->r1+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r10+
         r18->r12+
         r18->r14+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r12+
         r19->r13+
         r20->r0+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r8+
         r20->r12+
         r20->r13+
         r20->r18+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r9+
         r21->r14+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r7+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r6+
         r23->r8+
         r23->r14+
         r23->r17+
         r23->r18+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r25->r0+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r15+
         r25->r16+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r1+
         r26->r5+
         r26->r7+
         r26->r9+
         r26->r15+
         r26->r17+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r23+
         r26->r24+
         r27->r3+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r15+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r24+
         r27->r25+
         r28->r3+
         r28->r5+
         r28->r6+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r15+
         r28->r18+
         r28->r20+
         r28->r23+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r11+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r23+
         r29->r26}

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
    s =s20
    t =r5
    m = prohibition
    p = 2
    c = c5+c3
}
one sig rule1 extends Rule{}{
    s =s16
    t =r28
    m = prohibition
    p = 2
    c = c2+c9+c5
}
one sig rule2 extends Rule{}{
    s =s13
    t =r13
    m = prohibition
    p = 1
    c = c8+c4+c2+c9+c7
}
one sig rule3 extends Rule{}{
    s =s20
    t =r25
    m = permission
    p = 2
    c = c1+c5+c6+c3+c9+c8+c0
}
one sig rule4 extends Rule{}{
    s =s19
    t =r15
    m = permission
    p = 2
    c = c8+c4+c5+c3
}
one sig rule5 extends Rule{}{
    s =s17
    t =r22
    m = permission
    p = 2
    c = c5+c6+c0+c2+c8+c1
}
one sig rule6 extends Rule{}{
    s =s15
    t =r0
    m = prohibition
    p = 2
    c = c5+c3+c2+c6
}
one sig rule7 extends Rule{}{
    s =s20
    t =r29
    m = permission
    p = 2
    c = c3+c4+c8+c5
}
one sig rule8 extends Rule{}{
    s =s29
    t =r29
    m = prohibition
    p = 4
    c = c6+c1
}
one sig rule9 extends Rule{}{
    s =s9
    t =r12
    m = permission
    p = 1
    c = c7+c9+c8+c6+c5+c0
}
one sig rule10 extends Rule{}{
    s =s0
    t =r20
    m = permission
    p = 1
    c = c5+c1
}
one sig rule11 extends Rule{}{
    s =s21
    t =r6
    m = permission
    p = 0
    c = c5+c4+c9+c2+c1+c7
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

