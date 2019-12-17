module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s4->s3+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s5+
         s10->s8+
         s11->s1+
         s11->s8+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s12+
         s17->s1+
         s17->s4+
         s17->s11+
         s17->s14+
         s17->s16+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s12+
         s18->s14+
         s18->s16+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s17+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s4+
         s22->s9+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s3+
         s23->s5+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s19+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s9+
         s24->s11+
         s24->s14+
         s24->s17+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s3+
         s25->s6+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s18+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s9+
         s26->s12+
         s26->s14+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s27->s3+
         s27->s4+
         s27->s9+
         s27->s10+
         s27->s13+
         s27->s15+
         s27->s17+
         s27->s21+
         s27->s24+
         s27->s25+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s27+
         s29->s1+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s16+
         s29->s18+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s25+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r5+
         r11->r7+
         r11->r8+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r10+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r13+
         r15->r3+
         r15->r5+
         r15->r8+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r6+
         r17->r7+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r14+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r17+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r21->r0+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r8+
         r22->r10+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r19+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r5+
         r25->r10+
         r25->r11+
         r25->r16+
         r25->r17+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r8+
         r26->r9+
         r26->r11+
         r26->r13+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r22+
         r26->r23+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r6+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r13+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r22+
         r27->r23+
         r27->r26+
         r28->r1+
         r28->r3+
         r28->r7+
         r28->r8+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r20+
         r28->r21+
         r28->r23+
         r28->r24+
         r28->r25+
         r29->r0+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r8+
         r29->r10+
         r29->r13+
         r29->r17+
         r29->r18+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r24}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s3
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s26
    t =r14
    m = prohibition
    p = 4
    c = c1
}
one sig rule1 extends Rule{}{
    s =s9
    t =r11
    m = prohibition
    p = 3
    c = c3
}
one sig rule2 extends Rule{}{
    s =s21
    t =r0
    m = permission
    p = 3
    c = c5+c8+c4+c9+c3
}
one sig rule3 extends Rule{}{
    s =s24
    t =r14
    m = permission
    p = 0
    c = c3+c7+c0+c2+c9+c8+c1
}
one sig rule4 extends Rule{}{
    s =s16
    t =r28
    m = permission
    p = 2
    c = c8+c4+c1+c5
}
one sig rule5 extends Rule{}{
    s =s22
    t =r2
    m = prohibition
    p = 4
    c = c4+c8+c9+c0+c1+c2
}
one sig rule6 extends Rule{}{
    s =s23
    t =r27
    m = permission
    p = 0
    c = c9+c6+c2+c7+c0+c8+c1
}
one sig rule7 extends Rule{}{
    s =s7
    t =r23
    m = prohibition
    p = 1
    c = c5+c3
}
one sig rule8 extends Rule{}{
    s =s4
    t =r14
    m = prohibition
    p = 1
    c = c9+c0+c6
}
one sig rule9 extends Rule{}{
    s =s26
    t =r22
    m = prohibition
    p = 2
    c = c2+c0+c8+c7+c4
}
one sig rule10 extends Rule{}{
    s =s28
    t =r2
    m = permission
    p = 1
    c = c8
}
one sig rule11 extends Rule{}{
    s =s2
    t =r5
    m = prohibition
    p = 3
    c = c4+c6+c9+c2+c1+c5
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

