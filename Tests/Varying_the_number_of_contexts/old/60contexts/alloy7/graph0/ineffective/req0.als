module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s1+
         s4->s2+
         s5->s0+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s4+
         s7->s0+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s2+
         s15->s6+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s6+
         s16->s8+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s10+
         s17->s12+
         s17->s14+
         s18->s0+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s16+
         s19->s2+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s2+
         s20->s3+
         s20->s7+
         s20->s10+
         s20->s18+
         s21->s3+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s13+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s16+
         s22->s18+
         s22->s19+
         s23->s0+
         s23->s2+
         s23->s4+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s17+
         s23->s20+
         s24->s1+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s12+
         s24->s14+
         s24->s20+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s20+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s7+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s24+
         s27->s4+
         s27->s5+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s3+
         s28->s6+
         s28->s9+
         s28->s14+
         s28->s23+
         s28->s26+
         s28->s27+
         s29->s4+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r5+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r7+
         r10->r0+
         r11->r1+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r3+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r7+
         r13->r9+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r3+
         r17->r4+
         r17->r7+
         r17->r12+
         r17->r13+
         r17->r15+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r7+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r8+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r7+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r19+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r23->r0+
         r23->r1+
         r23->r4+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r15+
         r23->r17+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r2+
         r25->r5+
         r25->r6+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r22+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r9+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r25+
         r28->r0+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r22+
         r28->r25+
         r29->r1+
         r29->r2+
         r29->r5+
         r29->r7+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r20+
         r29->r22+
         r29->r25}

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
    s =s25
    t =r20
    m = prohibition
    p = 4
    c = c5+c1+c7+c9+c3
}
one sig rule1 extends Rule{}{
    s =s19
    t =r8
    m = prohibition
    p = 0
    c = c4+c5+c1+c7+c9
}
one sig rule2 extends Rule{}{
    s =s0
    t =r9
    m = prohibition
    p = 0
    c = c3+c0+c7+c8
}
one sig rule3 extends Rule{}{
    s =s14
    t =r18
    m = permission
    p = 2
    c = c6+c4+c0
}
one sig rule4 extends Rule{}{
    s =s23
    t =r11
    m = permission
    p = 3
    c = c7+c4+c5+c6+c0
}
one sig rule5 extends Rule{}{
    s =s29
    t =r5
    m = permission
    p = 0
    c = c0
}
one sig rule6 extends Rule{}{
    s =s10
    t =r15
    m = permission
    p = 3
    c = c1
}
one sig rule7 extends Rule{}{
    s =s12
    t =r5
    m = prohibition
    p = 3
    c = c2
}
one sig rule8 extends Rule{}{
    s =s16
    t =r15
    m = permission
    p = 3
    c = c2+c9+c0+c7
}
one sig rule9 extends Rule{}{
    s =s7
    t =r14
    m = permission
    p = 0
    c = c7+c5+c0+c3+c9+c8
}
one sig rule10 extends Rule{}{
    s =s4
    t =r22
    m = prohibition
    p = 0
    c = c2+c5+c4+c9
}
one sig rule11 extends Rule{}{
    s =s12
    t =r17
    m = prohibition
    p = 3
    c = c8+c9+c1
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

