module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s5->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s9->s0+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s3+
         s13->s8+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s7+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s12+
         s18->s13+
         s18->s15+
         s18->s16+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s18+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s8+
         s20->s9+
         s20->s12+
         s20->s13+
         s20->s17+
         s20->s18+
         s21->s2+
         s21->s6+
         s21->s11+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s18+
         s22->s19+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s6+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s24->s3+
         s24->s4+
         s24->s6+
         s24->s7+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s18+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s4+
         s25->s6+
         s25->s8+
         s25->s10+
         s25->s13+
         s25->s15+
         s25->s16+
         s25->s21+
         s25->s24+
         s26->s0+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s14+
         s26->s16+
         s26->s18+
         s26->s20+
         s26->s21+
         s26->s24+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s25+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s20+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s10+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s19+
         s29->s20+
         s29->s22}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r3->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r3+
         r11->r6+
         r11->r7+
         r11->r8+
         r12->r2+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r8+
         r14->r0+
         r14->r2+
         r14->r8+
         r14->r10+
         r14->r12+
         r15->r3+
         r15->r7+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r9+
         r16->r10+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r14+
         r17->r16+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r15+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r10+
         r20->r11+
         r20->r15+
         r20->r17+
         r20->r19+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r10+
         r21->r13+
         r21->r14+
         r21->r19+
         r21->r20+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r6+
         r23->r7+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r23+
         r25->r1+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r13+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r20+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r13+
         r26->r14+
         r26->r17+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r11+
         r27->r14+
         r27->r18+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r8+
         r28->r11+
         r28->r16+
         r28->r17+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r25+
         r28->r26+
         r29->r0+
         r29->r3+
         r29->r4+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r21+
         r29->r22+
         r29->r25+
         r29->r27}

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
    s =s22
    t =r16
    m = prohibition
    p = 2
    c = c9+c3+c8+c0
}
one sig rule1 extends Rule{}{
    s =s24
    t =r0
    m = permission
    p = 1
    c = c2+c9+c1+c8+c0+c6
}
one sig rule2 extends Rule{}{
    s =s5
    t =r20
    m = prohibition
    p = 4
    c = c4+c9+c7+c6+c1
}
one sig rule3 extends Rule{}{
    s =s23
    t =r2
    m = prohibition
    p = 0
    c = c4+c8+c5+c0
}
one sig rule4 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 3
    c = c5+c7+c8+c6+c0+c9
}
one sig rule5 extends Rule{}{
    s =s22
    t =r25
    m = prohibition
    p = 3
    c = c8+c0+c9
}
one sig rule6 extends Rule{}{
    s =s10
    t =r26
    m = permission
    p = 3
    c = c4+c7+c1
}
one sig rule7 extends Rule{}{
    s =s19
    t =r1
    m = permission
    p = 4
    c = c9
}
one sig rule8 extends Rule{}{
    s =s12
    t =r24
    m = prohibition
    p = 2
    c = c5+c6+c1+c0
}
one sig rule9 extends Rule{}{
    s =s26
    t =r14
    m = permission
    p = 3
    c = c3+c2+c6+c5+c0+c8
}
one sig rule10 extends Rule{}{
    s =s16
    t =r8
    m = permission
    p = 3
    c = c0+c8+c3+c9+c7+c1+c5
}
one sig rule11 extends Rule{}{
    s =s8
    t =r29
    m = permission
    p = 3
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

