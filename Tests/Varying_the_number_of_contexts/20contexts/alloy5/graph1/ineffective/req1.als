module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s4->s2+
         s5->s3+
         s5->s4+
         s6->s4+
         s7->s1+
         s7->s6+
         s8->s2+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s3+
         s11->s0+
         s11->s5+
         s11->s7+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s1+
         s16->s2+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s11+
         s16->s12+
         s17->s3+
         s17->s5+
         s17->s9+
         s17->s10+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s17+
         s19->s0+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s7+
         s20->s12+
         s20->s14+
         s20->s16+
         s20->s19+
         s21->s1+
         s21->s5+
         s21->s7+
         s21->s12+
         s21->s14+
         s21->s18+
         s22->s2+
         s22->s5+
         s22->s6+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s17+
         s22->s18+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s10+
         s23->s11+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s21+
         s23->s22+
         s24->s1+
         s24->s2+
         s24->s7+
         s24->s14+
         s24->s17+
         s24->s19+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s6+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s23+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s18+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s9+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s21+
         s27->s22+
         s28->s1+
         s28->s2+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s22+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s2+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r5+
         r9->r1+
         r9->r4+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r11+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r11+
         r15->r14+
         r16->r1+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r13+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r13+
         r19->r15+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r18+
         r21->r2+
         r21->r4+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r11+
         r22->r12+
         r22->r15+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r11+
         r23->r18+
         r23->r19+
         r23->r20+
         r24->r2+
         r24->r4+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r10+
         r25->r14+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r15+
         r26->r18+
         r26->r19+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r11+
         r27->r13+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r23+
         r28->r1+
         r28->r6+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r12+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r2+
         r29->r8+
         r29->r9+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r18+
         r29->r19+
         r29->r21+
         r29->r25+
         r29->r26}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19 extends Context{}{}

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
    s =s17
    t =r25
    m = permission
    p = 1
    c = c11+c4
}
one sig rule1 extends Rule{}{
    s =s3
    t =r9
    m = permission
    p = 0
    c = c4+c3+c11+c2+c9+c8+c19+c7+c1+c18
}
one sig rule2 extends Rule{}{
    s =s18
    t =r8
    m = prohibition
    p = 2
    c = c14+c4+c6+c11+c8+c12+c5+c10+c0+c2+c18+c1+c15+c13+c7
}
one sig rule3 extends Rule{}{
    s =s9
    t =r4
    m = permission
    p = 0
    c = c14+c16+c2+c12+c0+c11
}
one sig rule4 extends Rule{}{
    s =s4
    t =r23
    m = prohibition
    p = 1
    c = c17+c13+c3+c6+c5+c14+c7+c9+c4+c2+c16
}
one sig rule5 extends Rule{}{
    s =s22
    t =r11
    m = prohibition
    p = 2
    c = c11+c1+c7+c6
}
one sig rule6 extends Rule{}{
    s =s19
    t =r25
    m = permission
    p = 2
    c = c1+c9+c12+c18+c13+c15+c17+c3+c7+c5+c8+c11
}
one sig rule7 extends Rule{}{
    s =s16
    t =r9
    m = prohibition
    p = 4
    c = c7+c18+c6+c17+c19+c12
}
one sig rule8 extends Rule{}{
    s =s9
    t =r0
    m = prohibition
    p = 4
    c = c11+c13+c5+c17+c16+c3+c14+c0
}
one sig rule9 extends Rule{}{
    s =s2
    t =r14
    m = permission
    p = 1
    c = c1+c13+c3
}
one sig rule10 extends Rule{}{
    s =s9
    t =r28
    m = prohibition
    p = 2
    c = c3+c4+c19+c9+c0+c16+c2+c12+c7+c14+c6+c5+c8
}
one sig rule11 extends Rule{}{
    s =s0
    t =r4
    m = permission
    p = 1
    c = c16+c7+c3+c14+c15+c19+c13
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

