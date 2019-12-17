module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s2+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s4+
         s9->s1+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s10+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s7+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s7+
         s14->s10+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s5+
         s16->s9+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s15+
         s18->s16+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s14+
         s19->s15+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s2+
         s21->s4+
         s21->s6+
         s21->s8+
         s21->s11+
         s21->s14+
         s21->s18+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s15+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s16+
         s23->s18+
         s23->s20+
         s24->s3+
         s24->s4+
         s24->s8+
         s24->s9+
         s24->s15+
         s24->s17+
         s24->s20+
         s24->s21+
         s25->s4+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s16+
         s25->s17+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s1+
         s26->s2+
         s26->s5+
         s26->s10+
         s26->s15+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s2+
         s27->s6+
         s27->s7+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s4+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s18+
         s28->s20+
         s28->s23+
         s28->s25+
         s28->s27+
         s29->s1+
         s29->s3+
         s29->s6+
         s29->s8+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s15+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r3+
         r8->r2+
         r8->r3+
         r9->r1+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r6+
         r13->r8+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r12+
         r15->r0+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r13+
         r16->r0+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r14+
         r19->r15+
         r19->r17+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r10+
         r20->r15+
         r20->r17+
         r20->r19+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r20+
         r23->r1+
         r23->r3+
         r23->r5+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r22+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r19+
         r24->r20+
         r25->r0+
         r25->r7+
         r25->r10+
         r25->r12+
         r25->r18+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r8+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r21+
         r26->r24+
         r26->r25+
         r27->r2+
         r27->r3+
         r27->r5+
         r27->r7+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r16+
         r27->r18+
         r27->r20+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r8+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r24+
         r29->r6+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r19+
         r29->r20+
         r29->r23+
         r29->r24+
         r29->r25+
         r29->r26+
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
    t =r9
    m = permission
    p = 0
    c = c0+c6+c9+c1+c4+c2
}
one sig rule1 extends Rule{}{
    s =s27
    t =r9
    m = permission
    p = 0
    c = c6+c4+c7+c9+c1+c0
}
one sig rule2 extends Rule{}{
    s =s5
    t =r8
    m = prohibition
    p = 3
    c = c9+c4
}
one sig rule3 extends Rule{}{
    s =s23
    t =r0
    m = permission
    p = 4
    c = c8+c2+c9+c5
}
one sig rule4 extends Rule{}{
    s =s23
    t =r0
    m = permission
    p = 2
    c = c5+c4+c1+c9
}
one sig rule5 extends Rule{}{
    s =s9
    t =r21
    m = prohibition
    p = 0
    c = c2+c0+c5+c4
}
one sig rule6 extends Rule{}{
    s =s25
    t =r2
    m = permission
    p = 2
    c = c4+c9+c7+c2
}
one sig rule7 extends Rule{}{
    s =s13
    t =r8
    m = prohibition
    p = 1
    c = c6
}
one sig rule8 extends Rule{}{
    s =s0
    t =r29
    m = permission
    p = 3
    c = c3
}
one sig rule9 extends Rule{}{
    s =s29
    t =r29
    m = prohibition
    p = 2
    c = c4+c3+c5+c2
}
one sig rule10 extends Rule{}{
    s =s1
    t =r11
    m = permission
    p = 3
    c = c2
}
one sig rule11 extends Rule{}{
    s =s16
    t =r1
    m = prohibition
    p = 1
    c = c1+c3+c7+c2+c9+c8
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

