module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s2+
         s5->s0+
         s5->s3+
         s5->s4+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s6+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s5+
         s9->s8+
         s10->s4+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s7+
         s11->s10+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s14+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s4+
         s20->s6+
         s20->s8+
         s20->s11+
         s20->s13+
         s20->s15+
         s20->s17+
         s20->s18+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s7+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s21+
         s23->s2+
         s23->s9+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s22+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s16+
         s24->s18+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s4+
         s25->s6+
         s25->s8+
         s25->s11+
         s25->s12+
         s25->s17+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s1+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s12+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s17+
         s27->s18+
         s27->s21+
         s27->s23+
         s27->s26+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s12+
         s29->s18+
         s29->s21+
         s29->s22+
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
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r6+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r8+
         r13->r10+
         r14->r0+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r11+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r12+
         r17->r13+
         r18->r1+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r16+
         r19->r0+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r10+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r17+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r22->r1+
         r22->r2+
         r22->r8+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r18+
         r23->r1+
         r23->r2+
         r23->r4+
         r23->r7+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r20+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r8+
         r24->r10+
         r24->r13+
         r24->r19+
         r24->r20+
         r24->r23+
         r25->r4+
         r25->r7+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r21+
         r25->r22+
         r26->r2+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r20+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r16+
         r27->r17+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r20+
         r28->r21+
         r28->r25+
         r28->r26+
         r29->r1+
         r29->r2+
         r29->r5+
         r29->r9+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r23+
         r29->r24+
         r29->r26+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r0
    m = permission
    p = 0
    c = c9+c4+c2+c0
}
one sig rule1 extends Rule{}{
    s =s10
    t =r23
    m = permission
    p = 4
    c = c5+c7+c2+c9+c1
}
one sig rule2 extends Rule{}{
    s =s0
    t =r24
    m = permission
    p = 4
    c = c7+c6+c9
}
one sig rule3 extends Rule{}{
    s =s29
    t =r8
    m = permission
    p = 2
    c = c5+c1+c2+c4
}
one sig rule4 extends Rule{}{
    s =s0
    t =r9
    m = permission
    p = 4
    c = c4+c8+c0
}
one sig rule5 extends Rule{}{
    s =s28
    t =r3
    m = permission
    p = 1
    c = c9+c4+c2+c0+c3
}
one sig rule6 extends Rule{}{
    s =s16
    t =r15
    m = permission
    p = 1
    c = c7+c6+c0+c1+c2
}
one sig rule7 extends Rule{}{
    s =s2
    t =r23
    m = permission
    p = 4
    c = c1+c0+c6+c7+c2
}
one sig rule8 extends Rule{}{
    s =s23
    t =r29
    m = permission
    p = 0
    c = c9+c6
}
one sig rule9 extends Rule{}{
    s =s19
    t =r9
    m = permission
    p = 0
    c = c2
}
one sig rule10 extends Rule{}{
    s =s20
    t =r29
    m = permission
    p = 2
    c = c6+c7+c3+c8+c4+c9+c2
}
one sig rule11 extends Rule{}{
    s =s28
    t =r16
    m = prohibition
    p = 3
    c = c3
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

