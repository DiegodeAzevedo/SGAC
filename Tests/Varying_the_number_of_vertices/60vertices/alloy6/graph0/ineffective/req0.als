module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s4->s0+
         s5->s0+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s9+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s11+
         s14->s12+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s13+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s12+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s16+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s10+
         s21->s15+
         s21->s18+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s7+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s15+
         s22->s17+
         s22->s19+
         s22->s21+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s9+
         s23->s14+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s20+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s9+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s15+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s21+
         s25->s24+
         s26->s1+
         s26->s2+
         s26->s4+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s22+
         s26->s24+
         s27->s12+
         s27->s15+
         s27->s16+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s23+
         s27->s26+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s10+
         s28->s11+
         s28->s14+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s21+
         s28->s23+
         s28->s24+
         s28->s25+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s23+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r1+
         r6->r4+
         r7->r0+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r5+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r5+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r9+
         r12->r11+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r9+
         r15->r11+
         r15->r14+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r6+
         r18->r8+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r18+
         r20->r3+
         r20->r5+
         r20->r8+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r18+
         r21->r2+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r16+
         r21->r17+
         r21->r18+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r1+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r10+
         r23->r13+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r22+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r8+
         r24->r9+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r21+
         r25->r1+
         r25->r4+
         r25->r5+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r13+
         r25->r14+
         r25->r16+
         r25->r21+
         r26->r0+
         r26->r1+
         r26->r4+
         r26->r6+
         r26->r9+
         r26->r11+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r20+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r13+
         r27->r14+
         r27->r16+
         r27->r19+
         r27->r21+
         r27->r22+
         r27->r25+
         r27->r26+
         r28->r3+
         r28->r5+
         r28->r7+
         r28->r8+
         r28->r10+
         r28->r13+
         r28->r14+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r26+
         r29->r1+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r15+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r24+
         r29->r25+
         r29->r26+
         r29->r28}

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
    s =s12
    t =r4
    m = prohibition
    p = 1
    c = c5+c9+c4+c2
}
one sig rule1 extends Rule{}{
    s =s2
    t =r25
    m = prohibition
    p = 2
    c = c4
}
one sig rule2 extends Rule{}{
    s =s3
    t =r19
    m = prohibition
    p = 0
    c = c4+c8+c2+c0+c1
}
one sig rule3 extends Rule{}{
    s =s2
    t =r11
    m = prohibition
    p = 0
    c = c6+c8+c2+c0+c7+c5
}
one sig rule4 extends Rule{}{
    s =s18
    t =r5
    m = prohibition
    p = 4
    c = c9+c5+c1+c2
}
one sig rule5 extends Rule{}{
    s =s28
    t =r12
    m = prohibition
    p = 1
    c = c2+c0+c3+c7+c6+c4+c8
}
one sig rule6 extends Rule{}{
    s =s15
    t =r23
    m = prohibition
    p = 1
    c = c4+c1+c9
}
one sig rule7 extends Rule{}{
    s =s6
    t =r22
    m = prohibition
    p = 2
    c = c0
}
one sig rule8 extends Rule{}{
    s =s1
    t =r23
    m = permission
    p = 1
    c = c9+c7+c0+c2+c4
}
one sig rule9 extends Rule{}{
    s =s29
    t =r1
    m = permission
    p = 3
    c = c9+c7+c1+c0+c2+c8
}
one sig rule10 extends Rule{}{
    s =s8
    t =r28
    m = permission
    p = 2
    c = c6+c4
}
one sig rule11 extends Rule{}{
    s =s21
    t =r25
    m = permission
    p = 3
    c = c9+c6+c8
}
one sig rule12 extends Rule{}{
    s =s15
    t =r16
    m = permission
    p = 2
    c = c0
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

check ineffectiveRulerule12{ ineffectiveRule[rule12]}for 4

