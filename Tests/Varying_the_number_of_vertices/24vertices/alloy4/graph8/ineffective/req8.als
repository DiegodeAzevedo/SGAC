module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11 extends Subject{}{}
fact{
subSucc=s2->s1+
         s4->s2+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s2+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s1+
         s9->s4+
         s10->s0+
         s10->s3+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s9+
         s11->s10}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r3->r2+
         r5->r0+
         r5->r1+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r5+
         r11->r9}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req8 extends Request{}{
sub=s3
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r3
    m = prohibition
    p = 1
    c = c2+c4+c3+c6
}
one sig rule1 extends Rule{}{
    s =s5
    t =r4
    m = permission
    p = 4
    c = c8+c2+c4
}
one sig rule2 extends Rule{}{
    s =s8
    t =r0
    m = permission
    p = 0
    c = c6+c2+c7
}
one sig rule3 extends Rule{}{
    s =s9
    t =r11
    m = permission
    p = 2
    c = c7+c6+c1+c0+c3+c2
}
one sig rule4 extends Rule{}{
    s =s2
    t =r5
    m = prohibition
    p = 2
    c = c9+c8+c5+c3+c6+c7+c4
}
one sig rule5 extends Rule{}{
    s =s5
    t =r0
    m = prohibition
    p = 3
    c = c1+c5+c0+c2
}
one sig rule6 extends Rule{}{
    s =s0
    t =r0
    m = prohibition
    p = 0
    c = c4+c3+c6+c8
}
one sig rule7 extends Rule{}{
    s =s11
    t =r8
    m = prohibition
    p = 0
    c = c3+c6+c8+c4+c7
}
one sig rule8 extends Rule{}{
    s =s9
    t =r8
    m = permission
    p = 3
    c = c1+c7+c4+c6
}
one sig rule9 extends Rule{}{
    s =s7
    t =r3
    m = permission
    p = 4
    c = c1
}
one sig rule10 extends Rule{}{
    s =s6
    t =r2
    m = permission
    p = 0
    c = c5+c2+c1+c8+c4+c3+c0
}
one sig rule11 extends Rule{}{
    s =s7
    t =r4
    m = permission
    p = 2
    c = c0+c3+c5+c8+c6+c7
}
one sig rule12 extends Rule{}{
    s =s10
    t =r6
    m = prohibition
    p = 2
    c = c8+c4+c9+c1+c5
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

