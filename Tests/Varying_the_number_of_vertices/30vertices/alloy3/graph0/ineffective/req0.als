module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s2+
         s7->s0+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s3+
         s8->s5+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s3+
         s11->s4+
         s11->s5+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s6+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s13}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r6->r1+
         r6->r4+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r3+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r2+
         r13->r5+
         r13->r7+
         r13->r9+
         r14->r2+
         r14->r3+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12}

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
    s =s12
    t =r14
    m = permission
    p = 1
    c = c3+c7+c8+c1+c9+c6
}
one sig rule1 extends Rule{}{
    s =s13
    t =r10
    m = prohibition
    p = 2
    c = c1+c7+c8+c5+c3+c0
}
one sig rule2 extends Rule{}{
    s =s4
    t =r5
    m = prohibition
    p = 3
    c = c9+c4+c0+c8+c7
}
one sig rule3 extends Rule{}{
    s =s1
    t =r4
    m = prohibition
    p = 0
    c = c2+c4+c7+c6+c5+c0+c3
}
one sig rule4 extends Rule{}{
    s =s10
    t =r12
    m = prohibition
    p = 0
    c = c0
}
one sig rule5 extends Rule{}{
    s =s6
    t =r1
    m = permission
    p = 4
    c = c3+c9+c1+c2+c6+c8+c0
}
one sig rule6 extends Rule{}{
    s =s14
    t =r6
    m = permission
    p = 0
    c = c0+c4
}
one sig rule7 extends Rule{}{
    s =s14
    t =r0
    m = prohibition
    p = 1
    c = c0+c8+c2+c6+c1+c7+c4
}
one sig rule8 extends Rule{}{
    s =s11
    t =r13
    m = permission
    p = 4
    c = c4+c9+c7+c6
}
one sig rule9 extends Rule{}{
    s =s12
    t =r7
    m = prohibition
    p = 4
    c = c7+c2+c3+c0
}
one sig rule10 extends Rule{}{
    s =s12
    t =r2
    m = permission
    p = 4
    c = c6+c2+c3+c8+c7+c4
}
one sig rule11 extends Rule{}{
    s =s5
    t =r1
    m = prohibition
    p = 2
    c = c4+c2+c0+c1+c3
}
one sig rule12 extends Rule{}{
    s =s7
    t =r12
    m = prohibition
    p = 4
    c = c2+c0
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

