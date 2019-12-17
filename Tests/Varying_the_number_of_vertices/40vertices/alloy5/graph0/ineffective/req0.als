module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s4->s2+
         s5->s0+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s5+
         s11->s8+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s7+
         s13->s9+
         s14->s0+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s9+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s15+
         s18->s17+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r2+
         r8->r2+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r6+
         r10->r0+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r8+
         r14->r9+
         r14->r10+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r12+
         r15->r13+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r11+
         r17->r15+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18}

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
    s =s18
    t =r7
    m = prohibition
    p = 1
    c = c8+c6+c5+c1+c9+c0
}
one sig rule1 extends Rule{}{
    s =s11
    t =r1
    m = prohibition
    p = 2
    c = c4+c2+c7+c0+c9+c1+c3
}
one sig rule2 extends Rule{}{
    s =s15
    t =r14
    m = prohibition
    p = 0
    c = c8+c0+c7+c2
}
one sig rule3 extends Rule{}{
    s =s8
    t =r14
    m = prohibition
    p = 2
    c = c9+c4+c6
}
one sig rule4 extends Rule{}{
    s =s3
    t =r2
    m = permission
    p = 2
    c = c9+c1+c7+c3
}
one sig rule5 extends Rule{}{
    s =s15
    t =r8
    m = permission
    p = 2
    c = c5+c1+c4
}
one sig rule6 extends Rule{}{
    s =s8
    t =r9
    m = prohibition
    p = 0
    c = c2+c4+c5+c3+c1+c9+c6
}
one sig rule7 extends Rule{}{
    s =s4
    t =r10
    m = permission
    p = 4
    c = c9+c3+c5
}
one sig rule8 extends Rule{}{
    s =s14
    t =r1
    m = prohibition
    p = 3
    c = c7+c8
}
one sig rule9 extends Rule{}{
    s =s11
    t =r4
    m = prohibition
    p = 1
    c = c2+c0+c6+c5+c7+c1+c8
}
one sig rule10 extends Rule{}{
    s =s14
    t =r16
    m = permission
    p = 2
    c = c4+c1+c6+c2+c8+c9+c0
}
one sig rule11 extends Rule{}{
    s =s3
    t =r16
    m = prohibition
    p = 3
    c = c1+c7+c3
}
one sig rule12 extends Rule{}{
    s =s5
    t =r18
    m = permission
    p = 4
    c = c6+c9+c3+c8+c7+c5+c2
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

