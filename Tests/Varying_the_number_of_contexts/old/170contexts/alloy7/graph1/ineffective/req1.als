module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s6+
         s9->s0+
         s9->s4+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s6+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s13->s0+
         s13->s1+
         s13->s10+
         s14->s1+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s3+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s4+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s9+
         s18->s10+
         s19->s0+
         s19->s4+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s16+
         s19->s17+
         s20->s1+
         s20->s3+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s18+
         s20->s19+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s12+
         s22->s15+
         s22->s16+
         s22->s17+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s7+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s22+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s13+
         s25->s15+
         s25->s17+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s5+
         s26->s6+
         s26->s9+
         s26->s11+
         s26->s14+
         s26->s15+
         s26->s18+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s11+
         s27->s13+
         s27->s14+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s22+
         s27->s23+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s3+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s16+
         s29->s18+
         s29->s20+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r3+
         r8->r0+
         r8->r3+
         r8->r4+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r11->r0+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r9+
         r12->r1+
         r12->r4+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r10+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r4+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r4+
         r19->r5+
         r19->r10+
         r19->r12+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r6+
         r20->r7+
         r20->r10+
         r20->r11+
         r20->r14+
         r20->r16+
         r20->r18+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r10+
         r21->r11+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r10+
         r22->r11+
         r22->r14+
         r22->r19+
         r22->r21+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r14+
         r23->r18+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r6+
         r24->r7+
         r24->r16+
         r24->r18+
         r24->r19+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r12+
         r25->r15+
         r25->r17+
         r25->r22+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r7+
         r26->r8+
         r26->r11+
         r26->r12+
         r26->r16+
         r26->r19+
         r26->r21+
         r26->r22+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r4+
         r27->r6+
         r27->r9+
         r27->r11+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r24+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r9+
         r28->r12+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r24+
         r28->r25+
         r28->r26+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r6+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r20+
         r29->r23+
         r29->r24+
         r29->r28}

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
    t =r15
    m = permission
    p = 3
    c = c6+c9+c5+c4
}
one sig rule1 extends Rule{}{
    s =s16
    t =r8
    m = permission
    p = 0
    c = c3+c4+c7+c8
}
one sig rule2 extends Rule{}{
    s =s26
    t =r5
    m = permission
    p = 2
    c = c2+c6+c4+c7
}
one sig rule3 extends Rule{}{
    s =s14
    t =r24
    m = permission
    p = 3
    c = c0+c7+c4+c9+c8+c2
}
one sig rule4 extends Rule{}{
    s =s28
    t =r6
    m = prohibition
    p = 4
    c = c2+c9+c5+c3+c4
}
one sig rule5 extends Rule{}{
    s =s27
    t =r6
    m = permission
    p = 2
    c = c1+c5+c7+c3+c0+c9
}
one sig rule6 extends Rule{}{
    s =s12
    t =r17
    m = permission
    p = 3
    c = c4+c2+c1+c5+c0+c3+c8
}
one sig rule7 extends Rule{}{
    s =s19
    t =r6
    m = prohibition
    p = 1
    c = c4+c0+c5
}
one sig rule8 extends Rule{}{
    s =s16
    t =r22
    m = permission
    p = 2
    c = c9+c1+c3
}
one sig rule9 extends Rule{}{
    s =s18
    t =r11
    m = permission
    p = 2
    c = c9+c3+c8
}
one sig rule10 extends Rule{}{
    s =s0
    t =r23
    m = prohibition
    p = 2
    c = c8+c3+c2+c9
}
one sig rule11 extends Rule{}{
    s =s14
    t =r19
    m = prohibition
    p = 4
    c = c4+c3+c6+c2+c1
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

