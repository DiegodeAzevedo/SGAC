module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s4+
         s9->s1+
         s9->s2+
         s9->s5+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r2+
         r6->r0+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r9->r0+
         r9->r5+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r8+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r12}

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
    s =s13
    t =r7
    m = permission
    p = 3
    c = c5+c6+c0+c2
}
one sig rule1 extends Rule{}{
    s =s0
    t =r9
    m = prohibition
    p = 0
    c = c2+c0+c7+c9+c4
}
one sig rule2 extends Rule{}{
    s =s3
    t =r13
    m = permission
    p = 4
    c = c5+c7+c9+c6+c2
}
one sig rule3 extends Rule{}{
    s =s2
    t =r3
    m = permission
    p = 1
    c = c1+c0+c9+c2
}
one sig rule4 extends Rule{}{
    s =s14
    t =r13
    m = permission
    p = 0
    c = c2+c8+c7+c0+c3+c4
}
one sig rule5 extends Rule{}{
    s =s8
    t =r6
    m = permission
    p = 4
    c = c8+c5+c1+c7+c0
}
one sig rule6 extends Rule{}{
    s =s11
    t =r4
    m = prohibition
    p = 0
    c = c4
}
one sig rule7 extends Rule{}{
    s =s11
    t =r5
    m = prohibition
    p = 2
    c = c8+c6+c2+c7+c3+c4
}
one sig rule8 extends Rule{}{
    s =s1
    t =r10
    m = prohibition
    p = 1
    c = c8+c9+c1+c2+c3+c6
}
one sig rule9 extends Rule{}{
    s =s9
    t =r9
    m = prohibition
    p = 1
    c = c8+c9+c7+c2+c4+c0
}
one sig rule10 extends Rule{}{
    s =s13
    t =r12
    m = prohibition
    p = 0
    c = c2+c1+c0+c9+c7
}
one sig rule11 extends Rule{}{
    s =s8
    t =r5
    m = permission
    p = 1
    c = c8+c3
}
one sig rule12 extends Rule{}{
    s =s11
    t =r5
    m = prohibition
    p = 0
    c = c4+c7+c5
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

