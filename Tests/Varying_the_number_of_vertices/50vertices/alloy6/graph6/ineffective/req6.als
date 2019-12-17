module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s3+
         s5->s0+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s5+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s13->s0+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s11+
         s14->s12+
         s15->s1+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s14+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s6+
         s18->s7+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s11+
         s19->s16+
         s20->s0+
         s20->s6+
         s20->s7+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s16+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s16+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s3+
         s22->s6+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s17+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s7+
         s23->s8+
         s23->s11+
         s23->s15+
         s23->s18+
         s23->s21+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s15+
         s24->s17+
         s24->s18+
         s24->s21+
         s24->s22+
         s24->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r8+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r7+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r9+
         r13->r10+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r12+
         r17->r0+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r11+
         r19->r12+
         r19->r15+
         r19->r17+
         r20->r2+
         r20->r4+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r6+
         r21->r10+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r17+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r7+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r11+
         r23->r14+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r24->r0+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r16+
         r24->r17+
         r24->r21+
         r24->r23}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req6 extends Request{}{
sub=s7
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s23
    t =r0
    m = prohibition
    p = 3
    c = c5
}
one sig rule1 extends Rule{}{
    s =s15
    t =r10
    m = permission
    p = 2
    c = c5+c3+c7+c4+c6
}
one sig rule2 extends Rule{}{
    s =s24
    t =r16
    m = permission
    p = 3
    c = c3+c4+c0+c5
}
one sig rule3 extends Rule{}{
    s =s24
    t =r22
    m = prohibition
    p = 3
    c = c8+c3+c9+c1+c6
}
one sig rule4 extends Rule{}{
    s =s11
    t =r22
    m = prohibition
    p = 4
    c = c9+c4
}
one sig rule5 extends Rule{}{
    s =s16
    t =r5
    m = permission
    p = 1
    c = c4
}
one sig rule6 extends Rule{}{
    s =s4
    t =r7
    m = permission
    p = 2
    c = c2+c4+c9+c3
}
one sig rule7 extends Rule{}{
    s =s13
    t =r15
    m = prohibition
    p = 3
    c = c4+c9+c7+c1+c3+c8+c5
}
one sig rule8 extends Rule{}{
    s =s16
    t =r0
    m = permission
    p = 2
    c = c1+c8+c6+c4+c2
}
one sig rule9 extends Rule{}{
    s =s23
    t =r21
    m = prohibition
    p = 4
    c = c2+c3+c1+c7+c9
}
one sig rule10 extends Rule{}{
    s =s21
    t =r23
    m = prohibition
    p = 1
    c = c0+c4+c1
}
one sig rule11 extends Rule{}{
    s =s8
    t =r9
    m = permission
    p = 4
    c = c9+c2+c8+c7
}
one sig rule12 extends Rule{}{
    s =s12
    t =r3
    m = prohibition
    p = 2
    c = c5+c9+c8+c3
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

