module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s3->s2+
         s4->s2+
         s5->s1+
         s5->s3+
         s6->s0+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s2+
         s9->s4+
         s9->s7+
         s10->s1+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s8+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s2+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s3+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s11+
         s19->s14+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s5+
         s20->s9+
         s20->s11+
         s20->s16+
         s20->s17+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s23->s1+
         s23->s3+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s16+
         s24->s17+
         s24->s21+
         s24->s23+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s12+
         s25->s14+
         s25->s18+
         s25->s20+
         s25->s21+
         s26->s1+
         s26->s2+
         s26->s6+
         s26->s9+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s25+
         s27->s1+
         s27->s3+
         s27->s6+
         s27->s7+
         s27->s9+
         s27->s12+
         s27->s14+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s25+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s12+
         s28->s14+
         s28->s17+
         s28->s19+
         s28->s21+
         s28->s26+
         s29->s2+
         s29->s6+
         s29->s7+
         s29->s11+
         s29->s12+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s24+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r1+
         r6->r3+
         r7->r2+
         r8->r0+
         r8->r4+
         r8->r5+
         r9->r3+
         r9->r4+
         r9->r6+
         r10->r0+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r9+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r9+
         r14->r12+
         r15->r2+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r16->r1+
         r16->r3+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r8+
         r17->r11+
         r17->r13+
         r17->r15+
         r18->r7+
         r18->r14+
         r18->r15+
         r19->r2+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r5+
         r20->r6+
         r20->r10+
         r20->r13+
         r20->r16+
         r20->r19+
         r21->r0+
         r21->r3+
         r21->r9+
         r21->r11+
         r21->r12+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r19+
         r22->r0+
         r22->r4+
         r22->r7+
         r22->r12+
         r22->r13+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r6+
         r23->r7+
         r23->r9+
         r23->r12+
         r23->r14+
         r23->r16+
         r23->r18+
         r23->r21+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r6+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r16+
         r24->r20+
         r24->r22+
         r25->r3+
         r25->r5+
         r25->r8+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r22+
         r25->r24+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r14+
         r26->r18+
         r26->r20+
         r26->r21+
         r26->r23+
         r26->r25+
         r27->r1+
         r27->r3+
         r27->r4+
         r27->r6+
         r27->r8+
         r27->r13+
         r27->r15+
         r27->r16+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r14+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r25+
         r28->r26+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r8+
         r29->r10+
         r29->r12+
         r29->r16+
         r29->r21+
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
one sig req5 extends Request{}{
sub=s2
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s11
    t =r2
    m = permission
    p = 1
    c = c1+c9+c6
}
one sig rule1 extends Rule{}{
    s =s13
    t =r16
    m = prohibition
    p = 0
    c = c6+c8+c2
}
one sig rule2 extends Rule{}{
    s =s6
    t =r22
    m = prohibition
    p = 3
    c = c1+c5
}
one sig rule3 extends Rule{}{
    s =s12
    t =r21
    m = prohibition
    p = 0
    c = c9+c5+c8+c4+c0
}
one sig rule4 extends Rule{}{
    s =s0
    t =r16
    m = permission
    p = 2
    c = c5+c1+c6+c4+c7
}
one sig rule5 extends Rule{}{
    s =s26
    t =r18
    m = permission
    p = 3
    c = c5+c1+c2
}
one sig rule6 extends Rule{}{
    s =s23
    t =r24
    m = prohibition
    p = 3
    c = c9+c2+c8+c0
}
one sig rule7 extends Rule{}{
    s =s13
    t =r25
    m = prohibition
    p = 4
    c = c7
}
one sig rule8 extends Rule{}{
    s =s18
    t =r0
    m = permission
    p = 0
    c = c6
}
one sig rule9 extends Rule{}{
    s =s3
    t =r6
    m = prohibition
    p = 4
    c = c7+c4+c6+c9+c8
}
one sig rule10 extends Rule{}{
    s =s11
    t =r10
    m = prohibition
    p = 0
    c = c9+c3+c0
}
one sig rule11 extends Rule{}{
    s =s21
    t =r20
    m = prohibition
    p = 0
    c = c4+c6+c1+c3+c5+c0+c7
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

