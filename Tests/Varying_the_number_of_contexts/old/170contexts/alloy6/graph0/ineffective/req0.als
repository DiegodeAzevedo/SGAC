module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s15->s1+
         s15->s2+
         s15->s12+
         s15->s13+
         s16->s4+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s9+
         s18->s12+
         s18->s13+
         s18->s15+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17+
         s20->s2+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s13+
         s20->s14+
         s20->s17+
         s21->s2+
         s21->s5+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s18+
         s22->s19+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s4+
         s23->s10+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s16+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s6+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s18+
         s25->s20+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s3+
         s26->s8+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s18+
         s26->s19+
         s26->s21+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s24+
         s28->s0+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s19+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s1+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s23+
         s29->s25+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r5+
         r10->r7+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r5+
         r12->r7+
         r12->r8+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r6+
         r13->r7+
         r13->r10+
         r13->r12+
         r14->r4+
         r14->r5+
         r14->r8+
         r14->r9+
         r14->r13+
         r15->r1+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r6+
         r16->r10+
         r16->r11+
         r16->r15+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r11+
         r17->r12+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r16+
         r19->r1+
         r19->r3+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r14+
         r19->r17+
         r20->r0+
         r20->r4+
         r20->r6+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r14+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r9+
         r21->r10+
         r21->r13+
         r21->r14+
         r21->r17+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r9+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r17+
         r23->r1+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r14+
         r23->r15+
         r23->r19+
         r23->r20+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r11+
         r24->r14+
         r24->r16+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r8+
         r25->r9+
         r25->r13+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r16+
         r26->r17+
         r26->r19+
         r26->r20+
         r26->r23+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r5+
         r28->r6+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r15+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r23+
         r28->r24+
         r28->r26+
         r29->r2+
         r29->r3+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r13+
         r29->r16+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r25}

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
    s =s8
    t =r0
    m = prohibition
    p = 4
    c = c7+c2+c5+c8
}
one sig rule1 extends Rule{}{
    s =s22
    t =r10
    m = prohibition
    p = 0
    c = c8+c9
}
one sig rule2 extends Rule{}{
    s =s20
    t =r26
    m = permission
    p = 2
    c = c9+c3+c4
}
one sig rule3 extends Rule{}{
    s =s16
    t =r5
    m = permission
    p = 2
    c = c2
}
one sig rule4 extends Rule{}{
    s =s4
    t =r12
    m = permission
    p = 0
    c = c0+c2+c9+c3+c6
}
one sig rule5 extends Rule{}{
    s =s2
    t =r5
    m = permission
    p = 3
    c = c9+c6
}
one sig rule6 extends Rule{}{
    s =s17
    t =r29
    m = prohibition
    p = 2
    c = c4
}
one sig rule7 extends Rule{}{
    s =s8
    t =r22
    m = prohibition
    p = 2
    c = c8+c7
}
one sig rule8 extends Rule{}{
    s =s5
    t =r9
    m = prohibition
    p = 4
    c = c9+c3+c5+c4+c0
}
one sig rule9 extends Rule{}{
    s =s29
    t =r5
    m = prohibition
    p = 0
    c = c6+c4+c0+c9+c7+c1+c5+c2
}
one sig rule10 extends Rule{}{
    s =s16
    t =r22
    m = permission
    p = 3
    c = c5
}
one sig rule11 extends Rule{}{
    s =s3
    t =r14
    m = prohibition
    p = 1
    c = c6+c3+c7+c9+c1+c8
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

