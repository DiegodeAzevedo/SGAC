module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s2+
         s4->s2+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s7+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s6+
         s10->s7+
         s11->s3+
         s11->s4+
         s11->s9+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s11+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s11+
         s16->s15+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s6+
         s18->s9+
         s18->s12+
         s18->s13+
         s18->s17+
         s19->s2+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s14+
         s19->s18+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s9+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s18+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s16+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s11+
         s22->s14+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s5+
         s23->s6+
         s23->s9+
         s23->s13+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s7+
         s24->s10+
         s24->s11+
         s24->s15+
         s24->s17+
         s24->s18+
         s24->s21+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s6+
         s25->s14+
         s25->s19+
         s25->s23+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s5+
         s26->s8+
         s26->s9+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s20+
         s26->s21+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s24+
         s27->s25+
         s28->s1+
         s28->s2+
         s28->s4+
         s28->s5+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s1+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s21+
         s29->s24+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r2+
         r7->r4+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r6+
         r13->r10+
         r13->r11+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r16->r0+
         r16->r1+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r13+
         r19->r14+
         r19->r17+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r17+
         r21->r18+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r6+
         r22->r7+
         r22->r14+
         r22->r16+
         r22->r19+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r8+
         r23->r12+
         r23->r14+
         r23->r16+
         r23->r17+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r17+
         r24->r19+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r8+
         r25->r10+
         r25->r16+
         r25->r19+
         r25->r20+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r16+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r24+
         r27->r0+
         r27->r3+
         r27->r8+
         r27->r11+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r19+
         r27->r21+
         r28->r0+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r9+
         r28->r10+
         r28->r13+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r26+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r9+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r25+
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
    s =s9
    t =r22
    m = permission
    p = 4
    c = c1+c9+c5+c7+c0+c2
}
one sig rule1 extends Rule{}{
    s =s26
    t =r11
    m = permission
    p = 0
    c = c3+c5
}
one sig rule2 extends Rule{}{
    s =s13
    t =r25
    m = permission
    p = 3
    c = c2
}
one sig rule3 extends Rule{}{
    s =s26
    t =r19
    m = permission
    p = 2
    c = c3+c0+c8+c9
}
one sig rule4 extends Rule{}{
    s =s23
    t =r27
    m = prohibition
    p = 4
    c = c6+c8+c3+c1+c5
}
one sig rule5 extends Rule{}{
    s =s23
    t =r28
    m = permission
    p = 0
    c = c5
}
one sig rule6 extends Rule{}{
    s =s24
    t =r16
    m = prohibition
    p = 2
    c = c5+c1+c6+c3+c7+c0+c2
}
one sig rule7 extends Rule{}{
    s =s21
    t =r16
    m = prohibition
    p = 0
    c = c5+c9+c3+c2+c0
}
one sig rule8 extends Rule{}{
    s =s22
    t =r25
    m = prohibition
    p = 3
    c = c4+c9+c5+c7
}
one sig rule9 extends Rule{}{
    s =s17
    t =r3
    m = prohibition
    p = 2
    c = c9+c3+c5+c8+c4+c1
}
one sig rule10 extends Rule{}{
    s =s28
    t =r5
    m = permission
    p = 2
    c = c6+c1+c5+c4+c0+c7
}
one sig rule11 extends Rule{}{
    s =s15
    t =r3
    m = permission
    p = 2
    c = c7
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

