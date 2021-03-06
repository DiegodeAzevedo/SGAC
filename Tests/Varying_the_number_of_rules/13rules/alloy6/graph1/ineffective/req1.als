module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s4->s2+
         s5->s0+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s5+
         s8->s6+
         s9->s1+
         s9->s4+
         s9->s5+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s10+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s6+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r3->r2+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r5+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r2+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r7+
         r10->r8+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r5+
         r12->r8+
         r13->r2+
         r13->r4+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r5+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r3+
         r17->r6+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r10+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s3
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r6
    m = prohibition
    p = 0
    c = c5+c8+c0+c2+c1
}
one sig rule1 extends Rule{}{
    s =s1
    t =r19
    m = prohibition
    p = 1
    c = c4+c3+c2+c5+c1
}
one sig rule2 extends Rule{}{
    s =s3
    t =r6
    m = prohibition
    p = 2
    c = c1
}
one sig rule3 extends Rule{}{
    s =s12
    t =r15
    m = permission
    p = 4
    c = c8+c4+c7+c9+c6+c0+c3
}
one sig rule4 extends Rule{}{
    s =s0
    t =r0
    m = prohibition
    p = 1
    c = c0+c5+c7+c4+c9
}
one sig rule5 extends Rule{}{
    s =s16
    t =r12
    m = permission
    p = 3
    c = c0+c1+c2+c6+c7+c4
}
one sig rule6 extends Rule{}{
    s =s11
    t =r9
    m = permission
    p = 0
    c = c9+c5+c0+c4+c3+c8
}
one sig rule7 extends Rule{}{
    s =s17
    t =r14
    m = prohibition
    p = 2
    c = c2
}
one sig rule8 extends Rule{}{
    s =s17
    t =r13
    m = permission
    p = 1
    c = c2
}
one sig rule9 extends Rule{}{
    s =s13
    t =r0
    m = permission
    p = 2
    c = c2+c6
}
one sig rule10 extends Rule{}{
    s =s8
    t =r12
    m = permission
    p = 1
    c = c8+c5
}
one sig rule11 extends Rule{}{
    s =s6
    t =r0
    m = permission
    p = 1
    c = c8
}
one sig rule12 extends Rule{}{
    s =s13
    t =r0
    m = permission
    p = 2
    c = c1+c3+c4+c2
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

