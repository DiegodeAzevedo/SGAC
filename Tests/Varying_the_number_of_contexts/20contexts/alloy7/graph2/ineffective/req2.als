module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s3+
         s6->s0+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s4+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s15+
         s19->s0+
         s19->s1+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s6+
         s20->s8+
         s20->s10+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s10+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s10+
         s23->s13+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s20+
         s24->s1+
         s24->s11+
         s24->s16+
         s24->s20+
         s24->s21+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s9+
         s25->s12+
         s25->s13+
         s25->s15+
         s25->s18+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s6+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s9+
         s27->s11+
         s27->s14+
         s27->s15+
         s27->s23+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s8+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s3+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s11+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s22+
         s29->s23+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r2+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r5+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r14+
         r17->r2+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r16+
         r20->r0+
         r20->r3+
         r20->r8+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r18+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r16+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r8+
         r22->r10+
         r22->r12+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r20+
         r23->r1+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r16+
         r23->r18+
         r23->r19+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r7+
         r24->r9+
         r24->r15+
         r24->r16+
         r24->r19+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r6+
         r25->r8+
         r25->r10+
         r25->r18+
         r25->r19+
         r25->r23+
         r25->r24+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r15+
         r26->r17+
         r26->r21+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r25+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r8+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r16+
         r28->r22+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r10+
         r29->r13+
         r29->r14+
         r29->r26+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s24
    t =r9
    m = permission
    p = 4
    c = c7+c15+c5+c13+c18+c17
}
one sig rule1 extends Rule{}{
    s =s12
    t =r0
    m = permission
    p = 2
    c = c11+c18
}
one sig rule2 extends Rule{}{
    s =s3
    t =r6
    m = permission
    p = 4
    c = c10+c19+c2+c1+c15+c18+c3+c4+c8+c7+c14+c17
}
one sig rule3 extends Rule{}{
    s =s16
    t =r27
    m = prohibition
    p = 0
    c = c15+c7+c2+c5
}
one sig rule4 extends Rule{}{
    s =s12
    t =r13
    m = prohibition
    p = 0
    c = c11+c8+c12+c16+c4+c0+c14+c10+c13+c6
}
one sig rule5 extends Rule{}{
    s =s27
    t =r2
    m = permission
    p = 1
    c = c7+c9+c8+c6+c10+c17+c2+c16+c15+c5+c0+c4
}
one sig rule6 extends Rule{}{
    s =s19
    t =r1
    m = prohibition
    p = 3
    c = c2+c17+c1+c15+c12+c14+c18
}
one sig rule7 extends Rule{}{
    s =s4
    t =r5
    m = permission
    p = 4
    c = c16+c7+c15+c2+c1+c19+c6+c3+c9
}
one sig rule8 extends Rule{}{
    s =s29
    t =r1
    m = prohibition
    p = 0
    c = c1+c17+c7+c14+c8+c10+c2+c3+c0+c15
}
one sig rule9 extends Rule{}{
    s =s0
    t =r14
    m = prohibition
    p = 4
    c = c19+c6+c7+c1+c9+c4+c18+c16+c5+c12+c13+c11+c10
}
one sig rule10 extends Rule{}{
    s =s15
    t =r10
    m = prohibition
    p = 3
    c = c11+c13+c9+c10
}
one sig rule11 extends Rule{}{
    s =s12
    t =r12
    m = prohibition
    p = 0
    c = c15+c16+c0+c18+c19+c3
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

