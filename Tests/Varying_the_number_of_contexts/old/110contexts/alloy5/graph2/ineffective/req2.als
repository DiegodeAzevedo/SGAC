module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s5->s1+
         s5->s3+
         s6->s0+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s2+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s1+
         s10->s3+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s4+
         s15->s6+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s6+
         s16->s7+
         s16->s11+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s14+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s5+
         s19->s8+
         s19->s10+
         s19->s14+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s10+
         s20->s12+
         s20->s14+
         s20->s16+
         s20->s17+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s8+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s19+
         s22->s20+
         s23->s1+
         s23->s2+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s12+
         s23->s13+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s5+
         s24->s6+
         s24->s8+
         s24->s11+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s18+
         s24->s20+
         s24->s21+
         s25->s0+
         s25->s2+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s14+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s24+
         s26->s2+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s14+
         s26->s15+
         s26->s19+
         s26->s22+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s4+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s15+
         s27->s16+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s25+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s17+
         s28->s23+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s15+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r1+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r3+
         r7->r0+
         r7->r2+
         r7->r4+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r3+
         r9->r4+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r3+
         r11->r5+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r14->r2+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r11+
         r15->r14+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r15+
         r17->r2+
         r17->r4+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r10+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r16+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r10+
         r20->r12+
         r20->r15+
         r20->r16+
         r21->r1+
         r21->r3+
         r21->r7+
         r21->r9+
         r21->r16+
         r21->r19+
         r21->r20+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r5+
         r23->r6+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r15+
         r24->r16+
         r24->r18+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r10+
         r25->r11+
         r25->r13+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r21+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r4+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r28->r1+
         r28->r2+
         r28->r6+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r23+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r17+
         r29->r21+
         r29->r23+
         r29->r24+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r6
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s22
    t =r26
    m = permission
    p = 2
    c = c7+c2+c1+c3
}
one sig rule1 extends Rule{}{
    s =s28
    t =r0
    m = prohibition
    p = 3
    c = c5+c3+c1+c4
}
one sig rule2 extends Rule{}{
    s =s23
    t =r23
    m = prohibition
    p = 0
    c = c1+c9+c3+c7
}
one sig rule3 extends Rule{}{
    s =s21
    t =r29
    m = permission
    p = 4
    c = c9
}
one sig rule4 extends Rule{}{
    s =s2
    t =r26
    m = permission
    p = 4
    c = c9+c3+c8+c7
}
one sig rule5 extends Rule{}{
    s =s17
    t =r19
    m = permission
    p = 3
    c = c3+c1+c4+c5
}
one sig rule6 extends Rule{}{
    s =s28
    t =r6
    m = permission
    p = 2
    c = c9+c7+c2+c4
}
one sig rule7 extends Rule{}{
    s =s14
    t =r18
    m = prohibition
    p = 1
    c = c2+c0+c8+c6+c4+c9+c7
}
one sig rule8 extends Rule{}{
    s =s17
    t =r6
    m = prohibition
    p = 3
    c = c9+c5+c0+c8
}
one sig rule9 extends Rule{}{
    s =s29
    t =r6
    m = prohibition
    p = 3
    c = c3+c8+c9+c4
}
one sig rule10 extends Rule{}{
    s =s24
    t =r9
    m = permission
    p = 0
    c = c7+c5+c9+c1+c4+c3
}
one sig rule11 extends Rule{}{
    s =s23
    t =r3
    m = permission
    p = 3
    c = c3+c6+c2+c9+c7
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

