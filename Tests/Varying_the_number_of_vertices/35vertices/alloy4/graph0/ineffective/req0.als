module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s2+
         s4->s1+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s7->s0+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s7+
         s11->s9+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s4+
         s13->s6+
         s13->s9+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s15->s1+
         s15->s2+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s6+
         s16->s10+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r8+
         r10->r0+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15}

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
    t =r9
    m = permission
    p = 0
    c = c8+c7+c0+c4+c2+c1+c9
}
one sig rule1 extends Rule{}{
    s =s12
    t =r8
    m = prohibition
    p = 4
    c = c1+c5+c7+c9
}
one sig rule2 extends Rule{}{
    s =s13
    t =r3
    m = permission
    p = 1
    c = c6+c0+c8+c1+c2+c3+c5
}
one sig rule3 extends Rule{}{
    s =s0
    t =r6
    m = prohibition
    p = 0
    c = c2+c3+c5
}
one sig rule4 extends Rule{}{
    s =s11
    t =r2
    m = permission
    p = 3
    c = c3+c4+c6+c9+c8
}
one sig rule5 extends Rule{}{
    s =s3
    t =r8
    m = prohibition
    p = 4
    c = c1+c9+c8
}
one sig rule6 extends Rule{}{
    s =s3
    t =r16
    m = prohibition
    p = 4
    c = c6+c7+c1+c5+c3+c0
}
one sig rule7 extends Rule{}{
    s =s14
    t =r15
    m = prohibition
    p = 0
    c = c7+c4+c1
}
one sig rule8 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 1
    c = c1+c2+c0+c5
}
one sig rule9 extends Rule{}{
    s =s10
    t =r6
    m = prohibition
    p = 4
    c = c4+c8+c1+c2
}
one sig rule10 extends Rule{}{
    s =s6
    t =r16
    m = prohibition
    p = 1
    c = c8+c7+c3+c1+c4+c2
}
one sig rule11 extends Rule{}{
    s =s3
    t =r10
    m = permission
    p = 4
    c = c9+c5+c0+c2
}
one sig rule12 extends Rule{}{
    s =s7
    t =r14
    m = permission
    p = 1
    c = c6+c1
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

