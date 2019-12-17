module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s1+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s7+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s10+
         s14->s1+
         s14->s4+
         s14->s6+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s12+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s1+
         s17->s5+
         s17->s10+
         s17->s11+
         s17->s14+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s8+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s18+
         s21->s1+
         s21->s4+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s13+
         s22->s17+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s3+
         s23->s4+
         s23->s7+
         s23->s8+
         s23->s10+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s23+
         s25->s3+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s23+
         s25->s24+
         s26->s1+
         s26->s3+
         s26->s7+
         s26->s8+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s18+
         s26->s19+
         s26->s21+
         s26->s22+
         s27->s0+
         s27->s3+
         s27->s6+
         s27->s8+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s20+
         s27->s23+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s22+
         s28->s24+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r5+
         r9->r2+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r4+
         r12->r6+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r5+
         r13->r8+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r2+
         r15->r4+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r10+
         r16->r14+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r7+
         r17->r8+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r0+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r16+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r3+
         r21->r9+
         r21->r11+
         r21->r13+
         r21->r16+
         r21->r18+
         r22->r0+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r11+
         r23->r14+
         r23->r16+
         r23->r17+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r11+
         r25->r14+
         r25->r15+
         r25->r18+
         r25->r20+
         r25->r22+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r11+
         r26->r13+
         r26->r15+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r2+
         r27->r3+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r18+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r8+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r21+
         r28->r23+
         r28->r25+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r9+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r18+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r24+
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
    s =s28
    t =r8
    m = prohibition
    p = 3
    c = c2+c7+c1+c6+c0+c3
}
one sig rule1 extends Rule{}{
    s =s27
    t =r1
    m = permission
    p = 1
    c = c5+c2+c6+c7+c3+c4
}
one sig rule2 extends Rule{}{
    s =s23
    t =r27
    m = permission
    p = 3
    c = c7+c0+c8+c5+c1+c6
}
one sig rule3 extends Rule{}{
    s =s19
    t =r22
    m = permission
    p = 0
    c = c3+c8+c6+c5+c4
}
one sig rule4 extends Rule{}{
    s =s19
    t =r25
    m = permission
    p = 0
    c = c4+c7+c3+c1+c9+c5+c6
}
one sig rule5 extends Rule{}{
    s =s10
    t =r29
    m = prohibition
    p = 1
    c = c0+c8+c5+c3+c9+c1
}
one sig rule6 extends Rule{}{
    s =s4
    t =r10
    m = prohibition
    p = 4
    c = c8
}
one sig rule7 extends Rule{}{
    s =s8
    t =r25
    m = permission
    p = 4
    c = c9+c5+c1+c8
}
one sig rule8 extends Rule{}{
    s =s23
    t =r1
    m = permission
    p = 1
    c = c8+c3+c6+c4
}
one sig rule9 extends Rule{}{
    s =s6
    t =r12
    m = prohibition
    p = 1
    c = c4
}
one sig rule10 extends Rule{}{
    s =s16
    t =r10
    m = prohibition
    p = 3
    c = c2+c8+c0+c5+c4+c1+c7
}
one sig rule11 extends Rule{}{
    s =s19
    t =r20
    m = permission
    p = 1
    c = c0+c3+c9
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

