module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s4+
         s8->s5+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s10->s1+
         s10->s4+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s5+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s4+
         s13->s9+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s6+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s11+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s11+
         s18->s12+
         s18->s17+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s18+
         s20->s1+
         s20->s5+
         s20->s12+
         s20->s14+
         s20->s17+
         s20->s18+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s8+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s19+
         s23->s0+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s9+
         s23->s10+
         s23->s13+
         s23->s14+
         s23->s17+
         s23->s19+
         s23->s20+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s10+
         s24->s12+
         s24->s20+
         s24->s23+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s16+
         s25->s19+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s7+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s20+
         s26->s25+
         s27->s0+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s8+
         s27->s9+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s22+
         s27->s26+
         s28->s1+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s12+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s29->s0+
         s29->s1+
         s29->s4+
         s29->s6+
         s29->s8+
         s29->s11+
         s29->s18+
         s29->s20+
         s29->s21+
         s29->s24+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r4->r1+
         r4->r2+
         r5->r2+
         r6->r2+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r3+
         r9->r5+
         r9->r8+
         r10->r3+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r13+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r13+
         r19->r14+
         r20->r0+
         r20->r2+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r13+
         r20->r15+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r9+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r18+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r19+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r6+
         r25->r8+
         r25->r10+
         r25->r12+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r22+
         r25->r24+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r15+
         r27->r17+
         r27->r19+
         r27->r22+
         r27->r23+
         r28->r0+
         r28->r1+
         r28->r8+
         r28->r10+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r21+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r8+
         r29->r10+
         r29->r15+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r26+
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
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s25
    t =r16
    m = prohibition
    p = 3
    c = c6
}
one sig rule1 extends Rule{}{
    s =s1
    t =r26
    m = permission
    p = 1
    c = c6
}
one sig rule2 extends Rule{}{
    s =s3
    t =r7
    m = prohibition
    p = 0
    c = c4
}
one sig rule3 extends Rule{}{
    s =s22
    t =r20
    m = permission
    p = 2
    c = c5+c2+c4+c9+c1+c6+c7
}
one sig rule4 extends Rule{}{
    s =s26
    t =r11
    m = prohibition
    p = 4
    c = c9+c3+c8+c2
}
one sig rule5 extends Rule{}{
    s =s29
    t =r0
    m = prohibition
    p = 1
    c = c0+c5+c3+c4+c8+c9+c1
}
one sig rule6 extends Rule{}{
    s =s4
    t =r29
    m = prohibition
    p = 2
    c = c4+c0+c2+c1+c5
}
one sig rule7 extends Rule{}{
    s =s11
    t =r9
    m = prohibition
    p = 4
    c = c6+c4+c2
}
one sig rule8 extends Rule{}{
    s =s8
    t =r12
    m = permission
    p = 4
    c = c6
}
one sig rule9 extends Rule{}{
    s =s11
    t =r3
    m = permission
    p = 2
    c = c1+c2
}
one sig rule10 extends Rule{}{
    s =s24
    t =r14
    m = prohibition
    p = 2
    c = c2+c3+c4+c0+c1+c5
}
one sig rule11 extends Rule{}{
    s =s29
    t =r12
    m = prohibition
    p = 0
    c = c4+c7+c5+c3+c1+c2
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

