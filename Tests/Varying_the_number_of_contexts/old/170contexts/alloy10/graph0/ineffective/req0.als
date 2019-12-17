module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s4+
         s6->s2+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s6+
         s13->s7+
         s13->s10+
         s14->s1+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s14+
         s16->s1+
         s16->s6+
         s16->s7+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s15+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s11+
         s19->s14+
         s19->s16+
         s19->s17+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s17+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s14+
         s21->s15+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s3+
         s22->s5+
         s22->s8+
         s22->s11+
         s22->s16+
         s22->s17+
         s22->s19+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s13+
         s24->s18+
         s24->s22+
         s25->s0+
         s25->s4+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s17+
         s25->s20+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s4+
         s26->s7+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s18+
         s26->s20+
         s26->s22+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s7+
         s27->s11+
         s27->s18+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s25+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s11+
         s28->s12+
         s28->s15+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s24+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s4+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s23+
         s29->s24+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r7+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r7+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r11+
         r13->r12+
         r14->r4+
         r14->r5+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r3+
         r15->r6+
         r15->r8+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r4+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r13+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r10+
         r18->r12+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r16+
         r19->r17+
         r20->r1+
         r20->r5+
         r20->r8+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r2+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r17+
         r21->r18+
         r22->r0+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r14+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r16+
         r23->r19+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r21+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r10+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r20+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r1+
         r26->r3+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r1+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r9+
         r27->r10+
         r27->r14+
         r27->r20+
         r27->r21+
         r28->r1+
         r28->r2+
         r28->r4+
         r28->r6+
         r28->r8+
         r28->r11+
         r28->r14+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r3+
         r29->r5+
         r29->r7+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r20+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s11
    t =r2
    m = permission
    p = 3
    c = c6+c9+c3+c2+c0+c4
}
one sig rule1 extends Rule{}{
    s =s10
    t =r16
    m = permission
    p = 0
    c = c4+c6+c7+c1+c2+c8+c9+c3
}
one sig rule2 extends Rule{}{
    s =s28
    t =r0
    m = prohibition
    p = 0
    c = c8+c6+c5+c4+c9
}
one sig rule3 extends Rule{}{
    s =s15
    t =r10
    m = prohibition
    p = 4
    c = c3+c5+c2+c9+c8
}
one sig rule4 extends Rule{}{
    s =s22
    t =r2
    m = permission
    p = 4
    c = c4+c7+c9+c1+c0+c2
}
one sig rule5 extends Rule{}{
    s =s12
    t =r5
    m = prohibition
    p = 3
    c = c7+c3+c6+c4+c1+c0+c5
}
one sig rule6 extends Rule{}{
    s =s22
    t =r27
    m = prohibition
    p = 1
    c = c9+c3+c7+c5+c4
}
one sig rule7 extends Rule{}{
    s =s29
    t =r16
    m = prohibition
    p = 0
    c = c5+c2
}
one sig rule8 extends Rule{}{
    s =s23
    t =r7
    m = permission
    p = 1
    c = c2+c9+c7+c4+c8
}
one sig rule9 extends Rule{}{
    s =s16
    t =r20
    m = prohibition
    p = 0
    c = c4+c0
}
one sig rule10 extends Rule{}{
    s =s28
    t =r27
    m = permission
    p = 1
    c = c1+c4+c3+c5+c6+c8
}
one sig rule11 extends Rule{}{
    s =s9
    t =r4
    m = permission
    p = 1
    c = c7+c3+c8
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

