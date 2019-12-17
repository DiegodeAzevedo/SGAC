module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s3+
         s8->s4+
         s9->s0+
         s9->s1+
         s9->s4+
         s9->s5+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s7+
         s10->s8+
         s11->s1+
         s11->s2+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s9+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s18->s0+
         s18->s8+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s13+
         s19->s17+
         s20->s0+
         s20->s1+
         s20->s4+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s15+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s20+
         s22->s2+
         s22->s4+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s19+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s6+
         s23->s7+
         s23->s12+
         s23->s13+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s12+
         s24->s17+
         s24->s20+
         s24->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r10+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r11+
         r15->r13+
         r16->r10+
         r16->r11+
         r16->r15+
         r17->r3+
         r17->r7+
         r17->r11+
         r17->r13+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r13+
         r20->r16+
         r20->r17+
         r21->r0+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r16+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r4+
         r22->r5+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r4+
         r23->r6+
         r23->r8+
         r23->r11+
         r23->r12+
         r23->r18+
         r24->r0+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r9+
         r24->r12+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r20}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

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
    s =s20
    t =r16
    m = permission
    p = 3
    c = c8+c3+c1+c4+c2+c7
}
one sig rule1 extends Rule{}{
    s =s23
    t =r22
    m = permission
    p = 1
    c = c3+c7
}
one sig rule2 extends Rule{}{
    s =s11
    t =r9
    m = prohibition
    p = 0
    c = c9+c4+c3
}
one sig rule3 extends Rule{}{
    s =s15
    t =r14
    m = prohibition
    p = 0
    c = c8+c0+c5+c9
}
one sig rule4 extends Rule{}{
    s =s1
    t =r2
    m = permission
    p = 1
    c = c0+c6+c7+c4+c1+c5
}
one sig rule5 extends Rule{}{
    s =s1
    t =r10
    m = permission
    p = 4
    c = c1+c4+c6
}
one sig rule6 extends Rule{}{
    s =s13
    t =r22
    m = prohibition
    p = 4
    c = c8+c6+c3+c7+c2+c4
}
one sig rule7 extends Rule{}{
    s =s20
    t =r24
    m = permission
    p = 4
    c = c4+c6
}
one sig rule8 extends Rule{}{
    s =s11
    t =r23
    m = prohibition
    p = 1
    c = c0+c7+c6+c9+c4+c8
}
one sig rule9 extends Rule{}{
    s =s3
    t =r24
    m = prohibition
    p = 3
    c = c6+c7+c1+c8+c4
}
one sig rule10 extends Rule{}{
    s =s19
    t =r4
    m = permission
    p = 3
    c = c6+c4+c3+c1
}
one sig rule11 extends Rule{}{
    s =s15
    t =r23
    m = prohibition
    p = 1
    c = c7+c1+c0+c5+c3+c2
}
one sig rule12 extends Rule{}{
    s =s9
    t =r17
    m = permission
    p = 4
    c = c6+c9+c0+c7
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

