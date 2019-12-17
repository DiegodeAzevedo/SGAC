module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s7->s1+
         s7->s2+
         s7->s5+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s5+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s8+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s8+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s10+
         s14->s12+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s8+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s12+
         s17->s0+
         s17->s3+
         s17->s4+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s15+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s12+
         s19->s15+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s7+
         s20->s12+
         s20->s14+
         s20->s16+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s7+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s16+
         s22->s18+
         s22->s20}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r6+
         r8->r1+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r6+
         r11->r6+
         r11->r7+
         r11->r8+
         r12->r0+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r4+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r13+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r9+
         r18->r12+
         r18->r13+
         r18->r16+
         r19->r2+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r16+
         r19->r18+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r8+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r17+
         r21->r0+
         r21->r4+
         r21->r5+
         r21->r12+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r20}

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
    s =s1
    t =r3
    m = permission
    p = 2
    c = c6+c5+c4+c9
}
one sig rule1 extends Rule{}{
    s =s15
    t =r6
    m = permission
    p = 0
    c = c3+c9+c1+c7+c2+c4
}
one sig rule2 extends Rule{}{
    s =s1
    t =r21
    m = permission
    p = 2
    c = c1+c9+c3
}
one sig rule3 extends Rule{}{
    s =s18
    t =r2
    m = prohibition
    p = 3
    c = c9+c0
}
one sig rule4 extends Rule{}{
    s =s8
    t =r20
    m = prohibition
    p = 3
    c = c8+c6+c9+c4+c5
}
one sig rule5 extends Rule{}{
    s =s9
    t =r8
    m = prohibition
    p = 2
    c = c3+c2+c1+c9+c5
}
one sig rule6 extends Rule{}{
    s =s0
    t =r15
    m = permission
    p = 2
    c = c2
}
one sig rule7 extends Rule{}{
    s =s20
    t =r6
    m = permission
    p = 1
    c = c5+c3+c0+c8+c6+c7
}
one sig rule8 extends Rule{}{
    s =s1
    t =r11
    m = prohibition
    p = 0
    c = c4+c5+c7+c3+c0
}
one sig rule9 extends Rule{}{
    s =s20
    t =r21
    m = permission
    p = 0
    c = c7+c6+c1+c5+c2
}
one sig rule10 extends Rule{}{
    s =s1
    t =r4
    m = prohibition
    p = 0
    c = c3+c9+c1+c0+c4+c5+c2
}
one sig rule11 extends Rule{}{
    s =s4
    t =r5
    m = permission
    p = 3
    c = c9+c2+c3+c0
}
one sig rule12 extends Rule{}{
    s =s15
    t =r10
    m = prohibition
    p = 4
    c = c9+c1+c3+c4+c7+c2+c5
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

