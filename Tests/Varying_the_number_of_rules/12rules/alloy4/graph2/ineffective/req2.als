module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s2+
         s5->s1+
         s5->s2+
         s5->s3+
         s7->s1+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s9+
         s13->s3+
         s13->s5+
         s13->s8+
         s13->s11+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s10+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s10+
         s17->s12+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s8+
         s18->s11+
         s18->s12+
         s19->s0+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r4->r1+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r2+
         r6->r5+
         r7->r3+
         r7->r6+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r13+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r10+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r7+
         r19->r8+
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
sub=s6
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s0
    t =r8
    m = permission
    p = 1
    c = c5+c6+c2+c4+c9+c3
}
one sig rule1 extends Rule{}{
    s =s3
    t =r10
    m = permission
    p = 4
    c = c8+c7+c2+c9
}
one sig rule2 extends Rule{}{
    s =s3
    t =r10
    m = prohibition
    p = 1
    c = c7+c1+c0+c4+c2
}
one sig rule3 extends Rule{}{
    s =s13
    t =r16
    m = permission
    p = 4
    c = c5+c4+c7+c3+c2+c8
}
one sig rule4 extends Rule{}{
    s =s9
    t =r2
    m = permission
    p = 2
    c = c2+c7
}
one sig rule5 extends Rule{}{
    s =s5
    t =r9
    m = prohibition
    p = 3
    c = c6+c0+c9+c5+c4+c8+c1
}
one sig rule6 extends Rule{}{
    s =s14
    t =r0
    m = prohibition
    p = 4
    c = c0+c9+c5+c7+c2
}
one sig rule7 extends Rule{}{
    s =s13
    t =r7
    m = permission
    p = 3
    c = c4
}
one sig rule8 extends Rule{}{
    s =s16
    t =r19
    m = prohibition
    p = 3
    c = c8+c2+c0+c6
}
one sig rule9 extends Rule{}{
    s =s8
    t =r1
    m = prohibition
    p = 1
    c = c4+c9+c0+c7+c3
}
one sig rule10 extends Rule{}{
    s =s15
    t =r11
    m = prohibition
    p = 4
    c = c0+c7+c6+c8+c1+c9
}
one sig rule11 extends Rule{}{
    s =s0
    t =r11
    m = permission
    p = 3
    c = c1+c3+c5+c7+c8
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

