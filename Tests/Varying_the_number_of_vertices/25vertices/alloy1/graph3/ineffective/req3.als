module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s4+
         s7->s1+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s6+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s8}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r4->r0+
         r4->r1+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r6+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r6
    m = prohibition
    p = 2
    c = c2
}
one sig rule1 extends Rule{}{
    s =s1
    t =r0
    m = prohibition
    p = 3
    c = c8+c2+c5+c7+c3
}
one sig rule2 extends Rule{}{
    s =s0
    t =r8
    m = permission
    p = 2
    c = c2+c1+c8+c3
}
one sig rule3 extends Rule{}{
    s =s12
    t =r4
    m = prohibition
    p = 1
    c = c0+c4
}
one sig rule4 extends Rule{}{
    s =s6
    t =r10
    m = prohibition
    p = 3
    c = c7+c9+c2
}
one sig rule5 extends Rule{}{
    s =s11
    t =r1
    m = prohibition
    p = 4
    c = c0+c8+c7+c1+c2
}
one sig rule6 extends Rule{}{
    s =s6
    t =r6
    m = prohibition
    p = 1
    c = c8+c7+c0+c9+c6
}
one sig rule7 extends Rule{}{
    s =s0
    t =r6
    m = prohibition
    p = 1
    c = c4+c3+c7+c0+c5+c1
}
one sig rule8 extends Rule{}{
    s =s8
    t =r0
    m = permission
    p = 4
    c = c0+c9+c7+c2+c5+c3+c6
}
one sig rule9 extends Rule{}{
    s =s11
    t =r5
    m = prohibition
    p = 0
    c = c7+c1+c9
}
one sig rule10 extends Rule{}{
    s =s6
    t =r1
    m = prohibition
    p = 0
    c = c2+c3+c9+c0+c5
}
one sig rule11 extends Rule{}{
    s =s0
    t =r0
    m = permission
    p = 4
    c = c6+c8+c0+c5+c4+c3+c2+c9
}
one sig rule12 extends Rule{}{
    s =s5
    t =r2
    m = permission
    p = 4
    c = c5+c8+c0+c2
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

