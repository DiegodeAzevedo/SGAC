module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s2+
         s5->s0+
         s5->s1+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s1+
         s8->s2+
         s8->s7+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s5+
         s12->s7+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s8+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s6+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s15+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s15+
         s20->s2+
         s20->s3+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s23->s0+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s7+
         s23->s8+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s1+
         s24->s2+
         s24->s8+
         s24->s10+
         s24->s12+
         s24->s14+
         s24->s17+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s20+
         s26->s4+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s15+
         s26->s16+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s3+
         s27->s5+
         s27->s9+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s20+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s6+
         s28->s9+
         s28->s10+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s20+
         s28->s21+
         s28->s24+
         s28->s25+
         s28->s27+
         s29->s1+
         s29->s3+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s13+
         s29->s18+
         s29->s19+
         s29->s22+
         s29->s24+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r6+
         r8->r0+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r6+
         r11->r7+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r5+
         r13->r6+
         r13->r11+
         r14->r0+
         r14->r3+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r7+
         r16->r11+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r13+
         r19->r17+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r18+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r9+
         r21->r10+
         r21->r13+
         r21->r16+
         r21->r17+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r13+
         r22->r15+
         r22->r20+
         r23->r3+
         r23->r4+
         r23->r6+
         r23->r11+
         r23->r12+
         r23->r15+
         r23->r18+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r2+
         r24->r4+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r15+
         r24->r17+
         r24->r18+
         r24->r19+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r8+
         r25->r10+
         r25->r12+
         r25->r16+
         r25->r19+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r3+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r11+
         r26->r14+
         r26->r17+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r0+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r21+
         r27->r22+
         r27->r24+
         r27->r26+
         r28->r1+
         r28->r3+
         r28->r5+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r26+
         r29->r0+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r18}

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
    t =r1
    m = permission
    p = 0
    c = c2+c3+c5+c4+c0+c9
}
one sig rule1 extends Rule{}{
    s =s14
    t =r11
    m = prohibition
    p = 3
    c = c2+c5+c9+c6+c8
}
one sig rule2 extends Rule{}{
    s =s21
    t =r17
    m = permission
    p = 1
    c = c7+c4+c5+c3+c1+c6
}
one sig rule3 extends Rule{}{
    s =s13
    t =r1
    m = prohibition
    p = 2
    c = c4+c1+c7+c0+c8
}
one sig rule4 extends Rule{}{
    s =s16
    t =r2
    m = prohibition
    p = 4
    c = c2+c5+c3
}
one sig rule5 extends Rule{}{
    s =s10
    t =r12
    m = prohibition
    p = 4
    c = c3
}
one sig rule6 extends Rule{}{
    s =s7
    t =r20
    m = prohibition
    p = 1
    c = c6
}
one sig rule7 extends Rule{}{
    s =s25
    t =r6
    m = permission
    p = 3
    c = c0+c2+c7
}
one sig rule8 extends Rule{}{
    s =s20
    t =r24
    m = permission
    p = 3
    c = c6+c2+c8+c7
}
one sig rule9 extends Rule{}{
    s =s26
    t =r13
    m = prohibition
    p = 1
    c = c5+c6
}
one sig rule10 extends Rule{}{
    s =s10
    t =r7
    m = prohibition
    p = 2
    c = c4+c6+c7+c0+c3+c2
}
one sig rule11 extends Rule{}{
    s =s4
    t =r28
    m = permission
    p = 3
    c = c5+c4+c0+c7+c8+c3
}
one sig rule12 extends Rule{}{
    s =s8
    t =r21
    m = permission
    p = 2
    c = c0+c4+c3+c2
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

