module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s5->s0+
         s5->s1+
         s5->s2+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s4+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s7+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s4+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s2+
         s15->s5+
         s15->s7+
         s15->s10+
         s15->s14+
         s16->s0+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s4+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s17+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s6+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s16+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s16+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s12+
         s24->s15+
         s24->s17+
         s24->s19+
         s24->s21+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s8+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s16+
         s25->s20+
         s26->s1+
         s26->s2+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s11+
         s26->s12+
         s26->s15+
         s26->s17+
         s26->s19+
         s26->s23+
         s26->s24+
         s27->s1+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s12+
         s28->s14+
         s28->s19+
         s28->s23+
         s28->s24+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s12+
         s29->s13+
         s29->s18+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r5+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r9+
         r16->r12+
         r16->r13+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r14+
         r21->r0+
         r21->r3+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r14+
         r21->r15+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r1+
         r22->r2+
         r22->r5+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r17+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r10+
         r23->r11+
         r23->r14+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r4+
         r24->r8+
         r24->r9+
         r24->r12+
         r24->r16+
         r24->r22+
         r25->r4+
         r25->r7+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r1+
         r26->r5+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r15+
         r26->r18+
         r26->r22+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r6+
         r27->r7+
         r27->r12+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r2+
         r28->r4+
         r28->r7+
         r28->r9+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r26+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r10+
         r29->r14+
         r29->r17+
         r29->r18+
         r29->r22+
         r29->r25+
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
    s =s16
    t =r17
    m = prohibition
    p = 4
    c = c8+c7+c0+c1+c4+c2
}
one sig rule1 extends Rule{}{
    s =s18
    t =r8
    m = permission
    p = 4
    c = c7+c2+c6+c8+c5+c9
}
one sig rule2 extends Rule{}{
    s =s28
    t =r13
    m = permission
    p = 4
    c = c0+c2+c1
}
one sig rule3 extends Rule{}{
    s =s9
    t =r12
    m = prohibition
    p = 1
    c = c1+c9
}
one sig rule4 extends Rule{}{
    s =s24
    t =r0
    m = permission
    p = 3
    c = c3+c0+c8+c9
}
one sig rule5 extends Rule{}{
    s =s20
    t =r9
    m = permission
    p = 2
    c = c6+c7+c5+c4+c9+c0+c2
}
one sig rule6 extends Rule{}{
    s =s13
    t =r18
    m = permission
    p = 1
    c = c5+c3+c0+c2
}
one sig rule7 extends Rule{}{
    s =s23
    t =r7
    m = permission
    p = 1
    c = c4+c3+c9+c6+c5+c2
}
one sig rule8 extends Rule{}{
    s =s22
    t =r8
    m = permission
    p = 1
    c = c6
}
one sig rule9 extends Rule{}{
    s =s16
    t =r26
    m = prohibition
    p = 3
    c = c3+c9+c1
}
one sig rule10 extends Rule{}{
    s =s2
    t =r27
    m = permission
    p = 3
    c = c1
}
one sig rule11 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 4
    c = c3+c9+c7+c1+c5+c2+c0
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

