module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s7->s1+
         s7->s3+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s10+
         s13->s0+
         s13->s3+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s11+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s7+
         s15->s8+
         s15->s13+
         s16->s1+
         s16->s2+
         s16->s6+
         s16->s9+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s7+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s1+
         s18->s7+
         s18->s16+
         s19->s0+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s11+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s18+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s4+
         s22->s6+
         s22->s10+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s8+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s5+
         s24->s10+
         s24->s12+
         s24->s14+
         s24->s17+
         s24->s19+
         s24->s20+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s8+
         s25->s14+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s22+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s22+
         s26->s24+
         s27->s6+
         s27->s7+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s16+
         s27->s17+
         s27->s20+
         s27->s21+
         s27->s25+
         s27->s26+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s17+
         s28->s19+
         s28->s24+
         s28->s25+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s18+
         s29->s20+
         s29->s23+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r0+
         r5->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r4+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r6+
         r9->r7+
         r10->r4+
         r10->r8+
         r11->r7+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r6+
         r13->r10+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r16+
         r19->r18+
         r20->r3+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r11+
         r20->r14+
         r20->r18+
         r20->r19+
         r21->r2+
         r21->r5+
         r21->r8+
         r21->r9+
         r21->r13+
         r21->r14+
         r21->r18+
         r22->r0+
         r22->r1+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r18+
         r23->r20+
         r24->r0+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r17+
         r24->r18+
         r24->r21+
         r24->r23+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r6+
         r26->r8+
         r26->r11+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r22+
         r26->r23+
         r27->r1+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r7+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r4+
         r28->r6+
         r28->r8+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r5+
         r29->r8+
         r29->r9+
         r29->r14+
         r29->r15+
         r29->r17+
         r29->r20+
         r29->r27+
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
    s =s27
    t =r20
    m = prohibition
    p = 3
    c = c1+c2+c6+c5+c8+c4
}
one sig rule1 extends Rule{}{
    s =s14
    t =r24
    m = permission
    p = 4
    c = c1
}
one sig rule2 extends Rule{}{
    s =s27
    t =r29
    m = prohibition
    p = 3
    c = c8+c6+c4+c3+c9+c5+c1+c2
}
one sig rule3 extends Rule{}{
    s =s9
    t =r20
    m = prohibition
    p = 0
    c = c7+c6+c9+c0+c1
}
one sig rule4 extends Rule{}{
    s =s24
    t =r11
    m = prohibition
    p = 3
    c = c8
}
one sig rule5 extends Rule{}{
    s =s12
    t =r3
    m = prohibition
    p = 3
    c = c8+c3+c7
}
one sig rule6 extends Rule{}{
    s =s0
    t =r0
    m = permission
    p = 2
    c = c3+c6+c9+c8+c0+c4+c2
}
one sig rule7 extends Rule{}{
    s =s15
    t =r28
    m = prohibition
    p = 0
    c = c8+c7+c4+c0+c5+c6
}
one sig rule8 extends Rule{}{
    s =s22
    t =r19
    m = permission
    p = 1
    c = c2+c9+c8+c4
}
one sig rule9 extends Rule{}{
    s =s12
    t =r13
    m = prohibition
    p = 0
    c = c1+c9+c0
}
one sig rule10 extends Rule{}{
    s =s19
    t =r2
    m = permission
    p = 1
    c = c1+c8+c6+c5+c7+c9
}
one sig rule11 extends Rule{}{
    s =s24
    t =r17
    m = permission
    p = 1
    c = c5+c2+c1+c0
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

