module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s7+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s4+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s12+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s7+
         s18->s10+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s17+
         s20->s1+
         s20->s3+
         s20->s6+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s16+
         s22->s18+
         s22->s19+
         s22->s21+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s16+
         s23->s17+
         s23->s19+
         s24->s0+
         s24->s2+
         s24->s4+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s14+
         s24->s17+
         s24->s18+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s12+
         s25->s13+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s24+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s6+
         s26->s9+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s17+
         s26->s19+
         s26->s21+
         s26->s22+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s5+
         s27->s7+
         s27->s14+
         s27->s15+
         s27->s22+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s2+
         s28->s4+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s24+
         s28->s25+
         s29->s3+
         s29->s4+
         s29->s6+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r1+
         r11->r3+
         r11->r8+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r11+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r19+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r10+
         r21->r13+
         r21->r14+
         r21->r17+
         r21->r19+
         r22->r0+
         r22->r1+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r18+
         r22->r21+
         r23->r0+
         r23->r1+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r21+
         r24->r22+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r10+
         r25->r13+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r17+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r27->r2+
         r27->r3+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r14+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r6+
         r28->r11+
         r28->r20+
         r28->r21+
         r28->r25+
         r28->r26+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r24+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s26
    t =r20
    m = permission
    p = 0
    c = c4+c1+c0+c6+c7
}
one sig rule1 extends Rule{}{
    s =s6
    t =r18
    m = permission
    p = 4
    c = c7+c8+c9+c3+c6+c4+c0
}
one sig rule2 extends Rule{}{
    s =s2
    t =r29
    m = prohibition
    p = 2
    c = c6
}
one sig rule3 extends Rule{}{
    s =s26
    t =r23
    m = prohibition
    p = 3
    c = c5
}
one sig rule4 extends Rule{}{
    s =s7
    t =r27
    m = permission
    p = 3
    c = c0+c1+c5+c9+c3
}
one sig rule5 extends Rule{}{
    s =s27
    t =r24
    m = permission
    p = 4
    c = c3+c1+c5+c6+c9+c0
}
one sig rule6 extends Rule{}{
    s =s18
    t =r10
    m = permission
    p = 3
    c = c5+c7+c0
}
one sig rule7 extends Rule{}{
    s =s29
    t =r22
    m = permission
    p = 1
    c = c6+c1+c5+c0
}
one sig rule8 extends Rule{}{
    s =s21
    t =r28
    m = prohibition
    p = 0
    c = c5+c1+c4
}
one sig rule9 extends Rule{}{
    s =s15
    t =r29
    m = prohibition
    p = 2
    c = c1+c8+c9
}
one sig rule10 extends Rule{}{
    s =s27
    t =r17
    m = permission
    p = 0
    c = c5+c7+c4
}
one sig rule11 extends Rule{}{
    s =s11
    t =r25
    m = permission
    p = 4
    c = c2+c4+c3+c5+c6+c0+c8
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

