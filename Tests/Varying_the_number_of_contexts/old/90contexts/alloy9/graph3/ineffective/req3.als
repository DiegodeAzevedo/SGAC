module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s8+
         s13->s9+
         s13->s11+
         s14->s4+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s7+
         s15->s10+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s2+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s15+
         s19->s0+
         s19->s3+
         s19->s4+
         s19->s8+
         s19->s11+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s12+
         s21->s14+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s6+
         s22->s9+
         s22->s17+
         s22->s19+
         s22->s20+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s22+
         s24->s1+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s10+
         s24->s14+
         s24->s15+
         s24->s20+
         s24->s23+
         s25->s0+
         s25->s4+
         s25->s8+
         s25->s10+
         s25->s11+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s18+
         s25->s22+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s12+
         s26->s17+
         s26->s21+
         s27->s0+
         s27->s2+
         s27->s4+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s18+
         s27->s19+
         s27->s21+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s5+
         s28->s9+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r4->r3+
         r5->r2+
         r5->r4+
         r6->r2+
         r6->r3+
         r7->r1+
         r7->r2+
         r7->r6+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r2+
         r13->r6+
         r13->r7+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r11+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r13+
         r17->r0+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r12+
         r17->r14+
         r18->r1+
         r18->r3+
         r18->r5+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r17+
         r20->r1+
         r20->r6+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r15+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r22->r0+
         r22->r1+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r16+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r9+
         r23->r11+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r18+
         r23->r21+
         r24->r1+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r14+
         r24->r16+
         r24->r18+
         r24->r20+
         r24->r21+
         r25->r3+
         r25->r7+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r14+
         r25->r15+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r4+
         r26->r6+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r19+
         r26->r20+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r8+
         r27->r10+
         r27->r12+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r21+
         r27->r24+
         r28->r2+
         r28->r4+
         r28->r6+
         r28->r8+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r19+
         r28->r21+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r20+
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
one sig req3 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r14
    m = permission
    p = 0
    c = c5+c6+c3+c1+c4+c7
}
one sig rule1 extends Rule{}{
    s =s7
    t =r19
    m = prohibition
    p = 2
    c = c6+c1+c4+c9+c0
}
one sig rule2 extends Rule{}{
    s =s13
    t =r2
    m = permission
    p = 4
    c = c3+c2+c1+c9
}
one sig rule3 extends Rule{}{
    s =s11
    t =r13
    m = prohibition
    p = 3
    c = c1
}
one sig rule4 extends Rule{}{
    s =s12
    t =r29
    m = permission
    p = 3
    c = c0+c3+c4+c1
}
one sig rule5 extends Rule{}{
    s =s5
    t =r28
    m = permission
    p = 3
    c = c5+c1+c0+c8+c3
}
one sig rule6 extends Rule{}{
    s =s10
    t =r8
    m = prohibition
    p = 3
    c = c6+c5+c2
}
one sig rule7 extends Rule{}{
    s =s0
    t =r27
    m = prohibition
    p = 3
    c = c7+c3+c6+c9+c8+c2+c5
}
one sig rule8 extends Rule{}{
    s =s14
    t =r4
    m = permission
    p = 3
    c = c3+c7+c4+c6+c5+c1+c8
}
one sig rule9 extends Rule{}{
    s =s10
    t =r5
    m = permission
    p = 0
    c = c3+c9
}
one sig rule10 extends Rule{}{
    s =s16
    t =r20
    m = permission
    p = 3
    c = c9
}
one sig rule11 extends Rule{}{
    s =s25
    t =r5
    m = prohibition
    p = 3
    c = c7+c0+c4+c5+c6+c8
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

