module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s4+
         s6->s2+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s7+
         s13->s9+
         s13->s12+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s9+
         s15->s11+
         s15->s13+
         s16->s2+
         s16->s3+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s11+
         s19->s13+
         s20->s0+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s17+
         s20->s19+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s18+
         s22->s2+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s18+
         s22->s21+
         s23->s0+
         s23->s3+
         s23->s4+
         s23->s6+
         s23->s8+
         s23->s11+
         s23->s13+
         s23->s17+
         s23->s19+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s18+
         s24->s21+
         s24->s22+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s20+
         s25->s23+
         s26->s2+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s9+
         s26->s12+
         s26->s14+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s13+
         s27->s15+
         s27->s17+
         s27->s22+
         s27->s25+
         s28->s0+
         s28->s4+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s21+
         s28->s23+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s1+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s16+
         s29->s17+
         s29->s20+
         s29->s21+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r4+
         r10->r6+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r14->r2+
         r14->r3+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r12+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r19->r1+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r16+
         r20->r2+
         r20->r5+
         r20->r8+
         r20->r10+
         r20->r12+
         r20->r15+
         r20->r18+
         r20->r19+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r7+
         r22->r9+
         r22->r11+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r12+
         r23->r15+
         r23->r19+
         r24->r2+
         r24->r3+
         r24->r6+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r16+
         r24->r17+
         r24->r23+
         r25->r1+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r19+
         r25->r21+
         r25->r22+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r20+
         r26->r21+
         r26->r25+
         r27->r2+
         r27->r3+
         r27->r5+
         r27->r10+
         r27->r12+
         r27->r14+
         r27->r16+
         r27->r23+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r2+
         r28->r8+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r19+
         r28->r21+
         r28->r23+
         r28->r24+
         r29->r0+
         r29->r1+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r19+
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
one sig req1 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r29
    m = permission
    p = 2
    c = c4
}
one sig rule1 extends Rule{}{
    s =s21
    t =r2
    m = prohibition
    p = 4
    c = c0+c1
}
one sig rule2 extends Rule{}{
    s =s1
    t =r13
    m = permission
    p = 2
    c = c8+c7+c6+c2
}
one sig rule3 extends Rule{}{
    s =s26
    t =r23
    m = permission
    p = 2
    c = c5
}
one sig rule4 extends Rule{}{
    s =s25
    t =r11
    m = permission
    p = 0
    c = c1
}
one sig rule5 extends Rule{}{
    s =s22
    t =r18
    m = permission
    p = 4
    c = c1+c4
}
one sig rule6 extends Rule{}{
    s =s22
    t =r7
    m = prohibition
    p = 3
    c = c7
}
one sig rule7 extends Rule{}{
    s =s1
    t =r17
    m = prohibition
    p = 0
    c = c3+c6+c1+c4+c0+c8+c9
}
one sig rule8 extends Rule{}{
    s =s5
    t =r6
    m = prohibition
    p = 1
    c = c3+c4+c1+c7+c9
}
one sig rule9 extends Rule{}{
    s =s2
    t =r14
    m = prohibition
    p = 3
    c = c5+c0+c8+c6+c4
}
one sig rule10 extends Rule{}{
    s =s14
    t =r19
    m = prohibition
    p = 1
    c = c1+c4+c6+c2+c9+c8
}
one sig rule11 extends Rule{}{
    s =s20
    t =r18
    m = permission
    p = 1
    c = c7+c3+c6+c5+c1+c9
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

