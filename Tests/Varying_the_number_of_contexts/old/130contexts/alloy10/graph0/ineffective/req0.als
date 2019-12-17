module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s6->s0+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s6+
         s11->s7+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s2+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s4+
         s20->s7+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s18+
         s21->s0+
         s21->s3+
         s21->s5+
         s21->s7+
         s21->s8+
         s21->s13+
         s21->s14+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s4+
         s22->s7+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s17+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s11+
         s23->s13+
         s23->s21+
         s23->s22+
         s24->s3+
         s24->s5+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s15+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s23+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s7+
         s25->s11+
         s25->s12+
         s25->s16+
         s25->s19+
         s25->s20+
         s25->s22+
         s25->s24+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s12+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s25+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s6+
         s28->s9+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s18+
         s28->s20+
         s28->s23+
         s28->s24+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s16+
         s29->s18+
         s29->s20+
         s29->s21+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r11->r2+
         r11->r3+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r6+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r13+
         r17->r0+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r3+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r15+
         r19->r16+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r9+
         r21->r12+
         r21->r15+
         r21->r17+
         r22->r0+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r13+
         r22->r14+
         r22->r17+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r1+
         r23->r3+
         r23->r7+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r18+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r16+
         r24->r19+
         r24->r21+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r6+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r13+
         r25->r15+
         r25->r20+
         r25->r21+
         r25->r23+
         r26->r0+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r8+
         r26->r11+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r3+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r22+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r5+
         r28->r7+
         r28->r10+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r21+
         r28->r24+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r12+
         r29->r13+
         r29->r15+
         r29->r17+
         r29->r18+
         r29->r20+
         r29->r23+
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
    s =s1
    t =r2
    m = permission
    p = 2
    c = c6+c3+c4+c5+c7+c0+c9
}
one sig rule1 extends Rule{}{
    s =s15
    t =r27
    m = prohibition
    p = 2
    c = c1
}
one sig rule2 extends Rule{}{
    s =s24
    t =r29
    m = permission
    p = 2
    c = c9+c0+c3+c8+c7
}
one sig rule3 extends Rule{}{
    s =s2
    t =r28
    m = prohibition
    p = 0
    c = c1
}
one sig rule4 extends Rule{}{
    s =s20
    t =r25
    m = permission
    p = 4
    c = c6
}
one sig rule5 extends Rule{}{
    s =s12
    t =r20
    m = prohibition
    p = 2
    c = c7+c8+c2+c5+c1
}
one sig rule6 extends Rule{}{
    s =s2
    t =r29
    m = prohibition
    p = 2
    c = c9+c2+c4
}
one sig rule7 extends Rule{}{
    s =s23
    t =r22
    m = permission
    p = 0
    c = c1+c7+c3+c8+c2
}
one sig rule8 extends Rule{}{
    s =s2
    t =r16
    m = prohibition
    p = 3
    c = c1+c6+c9+c3+c7
}
one sig rule9 extends Rule{}{
    s =s27
    t =r9
    m = permission
    p = 2
    c = c6
}
one sig rule10 extends Rule{}{
    s =s29
    t =r12
    m = prohibition
    p = 0
    c = c3+c8+c4+c9+c5
}
one sig rule11 extends Rule{}{
    s =s15
    t =r0
    m = permission
    p = 1
    c = c0+c3+c8+c4
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

