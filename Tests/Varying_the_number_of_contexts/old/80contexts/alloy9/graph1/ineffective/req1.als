module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s6+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s4+
         s12->s6+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s9+
         s14->s12+
         s15->s2+
         s15->s4+
         s15->s7+
         s15->s9+
         s16->s1+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s7+
         s19->s10+
         s19->s12+
         s19->s15+
         s19->s16+
         s19->s17+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s7+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s15+
         s20->s16+
         s21->s1+
         s21->s4+
         s21->s5+
         s21->s10+
         s21->s11+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s10+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s4+
         s23->s7+
         s23->s15+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s8+
         s24->s10+
         s24->s12+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s7+
         s25->s9+
         s25->s11+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s9+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s19+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s4+
         s27->s7+
         s27->s8+
         s27->s11+
         s27->s13+
         s27->s18+
         s27->s19+
         s27->s25+
         s28->s2+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s10+
         s28->s12+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s21+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s19+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r3+
         r9->r0+
         r9->r1+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r6+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r1+
         r12->r4+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r5+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r16+
         r20->r0+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r12+
         r20->r14+
         r20->r16+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r6+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r16+
         r21->r19+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r19+
         r23->r1+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r16+
         r23->r18+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r5+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r24+
         r26->r0+
         r26->r3+
         r26->r4+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r20+
         r26->r21+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r8+
         r27->r11+
         r27->r14+
         r27->r17+
         r27->r24+
         r27->r25+
         r28->r2+
         r28->r3+
         r28->r5+
         r28->r6+
         r28->r12+
         r28->r14+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r25+
         r28->r27+
         r29->r6+
         r29->r9+
         r29->r12+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r24+
         r29->r25+
         r29->r26+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s28
    t =r15
    m = prohibition
    p = 3
    c = c0+c4+c3+c9+c5+c2
}
one sig rule1 extends Rule{}{
    s =s13
    t =r6
    m = prohibition
    p = 0
    c = c3
}
one sig rule2 extends Rule{}{
    s =s26
    t =r27
    m = permission
    p = 4
    c = c8+c2
}
one sig rule3 extends Rule{}{
    s =s3
    t =r14
    m = prohibition
    p = 2
    c = c5+c7+c6+c4+c0+c2+c3
}
one sig rule4 extends Rule{}{
    s =s19
    t =r17
    m = permission
    p = 4
    c = c7+c4+c0+c3+c8
}
one sig rule5 extends Rule{}{
    s =s11
    t =r25
    m = permission
    p = 0
    c = c5+c8+c4+c9+c2+c3
}
one sig rule6 extends Rule{}{
    s =s21
    t =r15
    m = permission
    p = 0
    c = c9+c7+c1+c3+c8
}
one sig rule7 extends Rule{}{
    s =s24
    t =r21
    m = permission
    p = 1
    c = c9+c4+c3+c5+c7
}
one sig rule8 extends Rule{}{
    s =s14
    t =r18
    m = prohibition
    p = 2
    c = c2
}
one sig rule9 extends Rule{}{
    s =s26
    t =r12
    m = prohibition
    p = 0
    c = c7+c9+c2+c0+c6+c3+c8+c1
}
one sig rule10 extends Rule{}{
    s =s11
    t =r17
    m = permission
    p = 2
    c = c6+c2
}
one sig rule11 extends Rule{}{
    s =s2
    t =r10
    m = permission
    p = 0
    c = c3+c4+c2+c1
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

