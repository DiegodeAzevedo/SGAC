module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s0+
         s8->s4+
         s8->s6+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s1+
         s19->s5+
         s19->s7+
         s19->s14+
         s19->s15+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s16+
         s20->s17+
         s20->s18+
         s21->s3+
         s21->s4+
         s21->s8+
         s21->s12+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s20+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s8+
         s22->s9+
         s22->s17+
         s22->s19+
         s22->s21+
         s23->s1+
         s23->s3+
         s23->s4+
         s23->s8+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s7+
         s24->s8+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s19+
         s24->s21+
         s24->s23+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s9+
         s25->s12+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s23+
         s25->s24+
         s26->s2+
         s26->s3+
         s26->s5+
         s26->s7+
         s26->s10+
         s26->s11+
         s26->s14+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s22+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s22+
         s28->s0+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s13+
         s28->s15+
         s28->s17+
         s28->s21+
         s28->s22+
         s28->s23+
         s29->s0+
         s29->s3+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s19+
         s29->s24+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r5->r4+
         r6->r3+
         r7->r1+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r5+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r4+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r6+
         r14->r8+
         r14->r11+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r6+
         r16->r8+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r17+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r14+
         r20->r18+
         r21->r3+
         r21->r4+
         r21->r9+
         r21->r12+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r12+
         r22->r13+
         r22->r16+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r6+
         r24->r7+
         r24->r12+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r13+
         r25->r14+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r21+
         r26->r24+
         r27->r0+
         r27->r3+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r14+
         r27->r17+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r9+
         r28->r10+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r25+
         r29->r0+
         r29->r3+
         r29->r6+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r19+
         r29->r21+
         r29->r22+
         r29->r24+
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
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s25
    t =r27
    m = permission
    p = 3
    c = c0
}
one sig rule1 extends Rule{}{
    s =s6
    t =r24
    m = prohibition
    p = 4
    c = c9+c5+c8+c1+c3+c6
}
one sig rule2 extends Rule{}{
    s =s18
    t =r27
    m = permission
    p = 2
    c = c1
}
one sig rule3 extends Rule{}{
    s =s0
    t =r19
    m = permission
    p = 3
    c = c1+c8+c0+c5
}
one sig rule4 extends Rule{}{
    s =s26
    t =r27
    m = prohibition
    p = 3
    c = c9+c4+c1+c0+c3+c8
}
one sig rule5 extends Rule{}{
    s =s27
    t =r15
    m = permission
    p = 0
    c = c7+c8
}
one sig rule6 extends Rule{}{
    s =s11
    t =r22
    m = prohibition
    p = 0
    c = c2+c7+c5
}
one sig rule7 extends Rule{}{
    s =s24
    t =r18
    m = permission
    p = 3
    c = c5+c6+c7+c0+c9+c4+c2
}
one sig rule8 extends Rule{}{
    s =s1
    t =r18
    m = permission
    p = 2
    c = c3+c9+c8+c4
}
one sig rule9 extends Rule{}{
    s =s1
    t =r25
    m = prohibition
    p = 3
    c = c7+c2+c0+c3+c8+c6
}
one sig rule10 extends Rule{}{
    s =s28
    t =r4
    m = permission
    p = 4
    c = c9+c6+c2+c8
}
one sig rule11 extends Rule{}{
    s =s24
    t =r2
    m = prohibition
    p = 2
    c = c1+c6+c3+c4+c0+c2
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

