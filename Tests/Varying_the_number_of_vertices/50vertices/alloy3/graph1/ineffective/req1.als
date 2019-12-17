module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s1+
         s4->s2+
         s5->s2+
         s6->s0+
         s6->s3+
         s6->s4+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s1+
         s10->s4+
         s10->s6+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s10+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s6+
         s13->s8+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s5+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s1+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s11+
         s15->s13+
         s16->s2+
         s16->s3+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s10+
         s18->s12+
         s18->s14+
         s18->s15+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s16+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s7+
         s21->s11+
         s21->s12+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s17+
         s22->s19+
         s22->s20+
         s23->s3+
         s23->s4+
         s23->s12+
         s23->s14+
         s23->s17+
         s23->s18+
         s24->s0+
         s24->s1+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s14+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s21}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r5->r1+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r4+
         r7->r5+
         r8->r1+
         r8->r2+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r7+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r12+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r7+
         r19->r8+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r8+
         r22->r10+
         r22->r11+
         r22->r16+
         r22->r17+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r1+
         r23->r3+
         r23->r4+
         r23->r6+
         r23->r7+
         r23->r10+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r8+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r22}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r5
    m = permission
    p = 4
    c = c6+c7+c5+c4+c8+c1+c0
}
one sig rule1 extends Rule{}{
    s =s23
    t =r2
    m = prohibition
    p = 4
    c = c2+c8+c6+c4+c1
}
one sig rule2 extends Rule{}{
    s =s7
    t =r12
    m = permission
    p = 3
    c = c6+c2+c3+c1+c8+c7+c4
}
one sig rule3 extends Rule{}{
    s =s3
    t =r15
    m = prohibition
    p = 0
    c = c7+c1
}
one sig rule4 extends Rule{}{
    s =s12
    t =r24
    m = prohibition
    p = 0
    c = c4+c5+c0+c1
}
one sig rule5 extends Rule{}{
    s =s15
    t =r5
    m = permission
    p = 0
    c = c4
}
one sig rule6 extends Rule{}{
    s =s7
    t =r19
    m = prohibition
    p = 2
    c = c4+c5+c1+c3+c8
}
one sig rule7 extends Rule{}{
    s =s19
    t =r20
    m = prohibition
    p = 4
    c = c7+c6+c2+c1+c4+c5
}
one sig rule8 extends Rule{}{
    s =s0
    t =r12
    m = permission
    p = 0
    c = c3+c9
}
one sig rule9 extends Rule{}{
    s =s21
    t =r24
    m = prohibition
    p = 2
    c = c4
}
one sig rule10 extends Rule{}{
    s =s24
    t =r24
    m = permission
    p = 4
    c = c0+c4+c1+c2
}
one sig rule11 extends Rule{}{
    s =s3
    t =r4
    m = prohibition
    p = 0
    c = c1
}
one sig rule12 extends Rule{}{
    s =s12
    t =r18
    m = permission
    p = 2
    c = c5+c9+c8+c7+c2+c3
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

