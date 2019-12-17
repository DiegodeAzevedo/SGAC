module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s1+
         s3->s2+
         s5->s0+
         s6->s0+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s7+
         s9->s2+
         s9->s4+
         s9->s6+
         s10->s1+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s6+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s6+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s3+
         s15->s5+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s14+
         s17->s4+
         s17->s6+
         s17->s9+
         s17->s12+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s6+
         s18->s7+
         s18->s10+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r2+
         r6->r1+
         r6->r4+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r4+
         r9->r6+
         r10->r0+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r8+
         r12->r0+
         r12->r2+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r10+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r15+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r11+
         r19->r14+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s4
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r0
    m = permission
    p = 0
    c = c7+c4+c1+c2
}
one sig rule1 extends Rule{}{
    s =s5
    t =r10
    m = permission
    p = 0
    c = c9+c1+c3+c8+c2
}
one sig rule2 extends Rule{}{
    s =s1
    t =r17
    m = prohibition
    p = 1
    c = c4+c3+c1
}
one sig rule3 extends Rule{}{
    s =s11
    t =r5
    m = permission
    p = 3
    c = c2+c6
}
one sig rule4 extends Rule{}{
    s =s19
    t =r0
    m = prohibition
    p = 0
    c = c0+c4+c7
}
one sig rule5 extends Rule{}{
    s =s13
    t =r11
    m = prohibition
    p = 4
    c = c6+c2+c8+c5+c1
}
one sig rule6 extends Rule{}{
    s =s8
    t =r17
    m = prohibition
    p = 4
    c = c8+c6+c3+c5+c2+c4
}
one sig rule7 extends Rule{}{
    s =s13
    t =r13
    m = prohibition
    p = 2
    c = c8
}
one sig rule8 extends Rule{}{
    s =s14
    t =r15
    m = permission
    p = 2
    c = c5
}
one sig rule9 extends Rule{}{
    s =s18
    t =r5
    m = prohibition
    p = 0
    c = c4+c3+c7+c1+c8+c5
}
one sig rule10 extends Rule{}{
    s =s13
    t =r16
    m = prohibition
    p = 4
    c = c3
}
one sig rule11 extends Rule{}{
    s =s5
    t =r15
    m = permission
    p = 0
    c = c4+c2+c1+c7+c9+c3+c0
}
one sig rule12 extends Rule{}{
    s =s4
    t =r8
    m = prohibition
    p = 2
    c = c7+c1+c2+c0
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

