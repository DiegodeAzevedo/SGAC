module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s9->s1+
         s9->s2+
         s9->s5+
         s9->s7+
         s10->s3+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s5+
         s13->s6+
         s13->s10+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s7+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s12+
         s16->s14+
         s17->s1+
         s17->s4+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s16+
         s18->s1+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s5+
         s19->s8+
         s19->s11+
         s19->s13+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r5->r2+
         r6->r3+
         r6->r4+
         r7->r2+
         r7->r3+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r8+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r9+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r11+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r11+
         r15->r14+
         r16->r0+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r1+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r10+
         r19->r12+
         r19->r14+
         r19->r16+
         r19->r17}

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
    s =s3
    t =r8
    m = prohibition
    p = 0
    c = c7
}
one sig rule1 extends Rule{}{
    s =s6
    t =r18
    m = permission
    p = 1
    c = c8+c6+c2
}
one sig rule2 extends Rule{}{
    s =s5
    t =r16
    m = prohibition
    p = 4
    c = c1+c4+c6+c3+c7+c9+c0
}
one sig rule3 extends Rule{}{
    s =s12
    t =r7
    m = prohibition
    p = 0
    c = c9+c5+c7
}
one sig rule4 extends Rule{}{
    s =s16
    t =r3
    m = permission
    p = 3
    c = c8+c4+c1+c3
}
one sig rule5 extends Rule{}{
    s =s12
    t =r10
    m = prohibition
    p = 0
    c = c6+c7+c2+c0
}
one sig rule6 extends Rule{}{
    s =s14
    t =r18
    m = prohibition
    p = 3
    c = c8+c7
}
one sig rule7 extends Rule{}{
    s =s10
    t =r10
    m = prohibition
    p = 0
    c = c8+c5+c6+c4
}
one sig rule8 extends Rule{}{
    s =s19
    t =r10
    m = permission
    p = 0
    c = c9+c0+c6
}
one sig rule9 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 3
    c = c8+c5+c1+c9+c2+c7
}
one sig rule10 extends Rule{}{
    s =s10
    t =r15
    m = permission
    p = 4
    c = c9+c1+c5+c0
}
one sig rule11 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 0
    c = c5+c7
}
one sig rule12 extends Rule{}{
    s =s7
    t =r8
    m = permission
    p = 3
    c = c9+c4+c2+c6+c7+c0
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

