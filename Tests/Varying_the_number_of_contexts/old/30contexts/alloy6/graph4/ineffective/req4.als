module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s7->s4+
         s8->s1+
         s8->s3+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s7+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s11+
         s13->s1+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s11+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s5+
         s18->s7+
         s18->s11+
         s18->s16+
         s19->s6+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s15+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s12+
         s21->s13+
         s21->s16+
         s21->s18+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s4+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s14+
         s23->s16+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s6+
         s25->s8+
         s25->s11+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s19+
         s25->s20+
         s25->s22+
         s26->s3+
         s26->s6+
         s26->s10+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s3+
         s27->s4+
         s27->s7+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s22+
         s27->s25+
         s28->s0+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s9+
         s28->s15+
         s28->s18+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s12+
         s29->s14+
         s29->s16+
         s29->s20+
         s29->s21+
         s29->s24+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r4+
         r6->r1+
         r6->r2+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r3+
         r11->r5+
         r12->r0+
         r12->r5+
         r12->r9+
         r12->r10+
         r13->r3+
         r13->r4+
         r13->r8+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r9+
         r15->r12+
         r16->r0+
         r16->r2+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r10+
         r17->r11+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r5+
         r18->r11+
         r18->r13+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r16+
         r19->r18+
         r20->r1+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r15+
         r21->r17+
         r21->r18+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r17+
         r22->r18+
         r22->r20+
         r23->r1+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r4+
         r25->r5+
         r25->r7+
         r25->r8+
         r25->r11+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r21+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r14+
         r26->r16+
         r26->r18+
         r26->r19+
         r26->r22+
         r26->r23+
         r27->r0+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r15+
         r27->r16+
         r27->r19+
         r27->r21+
         r27->r22+
         r27->r24+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r7+
         r28->r9+
         r28->r11+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r25+
         r29->r1+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r19+
         r29->r21+
         r29->r23+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s3
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s27
    t =r28
    m = prohibition
    p = 2
    c = c1+c7+c2+c6+c9
}
one sig rule1 extends Rule{}{
    s =s16
    t =r15
    m = prohibition
    p = 1
    c = c7+c4+c1+c2
}
one sig rule2 extends Rule{}{
    s =s4
    t =r23
    m = prohibition
    p = 0
    c = c2+c8+c0+c6+c9+c3+c1
}
one sig rule3 extends Rule{}{
    s =s7
    t =r26
    m = prohibition
    p = 3
    c = c1
}
one sig rule4 extends Rule{}{
    s =s18
    t =r26
    m = permission
    p = 2
    c = c1+c5+c0+c3
}
one sig rule5 extends Rule{}{
    s =s23
    t =r12
    m = permission
    p = 3
    c = c0+c6+c8+c7+c4+c1
}
one sig rule6 extends Rule{}{
    s =s22
    t =r19
    m = prohibition
    p = 2
    c = c3+c4+c5+c6
}
one sig rule7 extends Rule{}{
    s =s13
    t =r16
    m = permission
    p = 4
    c = c6+c1+c0+c8
}
one sig rule8 extends Rule{}{
    s =s2
    t =r13
    m = prohibition
    p = 3
    c = c1+c4+c8+c2
}
one sig rule9 extends Rule{}{
    s =s6
    t =r18
    m = permission
    p = 1
    c = c5+c0+c9+c8
}
one sig rule10 extends Rule{}{
    s =s9
    t =r25
    m = permission
    p = 4
    c = c1+c2+c9+c8
}
one sig rule11 extends Rule{}{
    s =s11
    t =r14
    m = permission
    p = 3
    c = c6+c8+c0+c7+c5
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

