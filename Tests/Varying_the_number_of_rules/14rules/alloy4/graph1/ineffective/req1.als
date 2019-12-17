module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s5+
         s9->s6+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s11+
         s13->s2+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s9+
         s14->s12+
         s15->s1+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s11+
         s17->s12+
         s17->s13+
         s18->s0+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s3+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r1+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r10->r5+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r8+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r11+
         r14->r12+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r10+
         r17->r11+
         r17->r16+
         r18->r2+
         r18->r4+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r9
    m = prohibition
    p = 1
    c = c4+c0+c2+c8
}
one sig rule1 extends Rule{}{
    s =s13
    t =r19
    m = permission
    p = 1
    c = c8+c4+c3+c9+c1+c5
}
one sig rule2 extends Rule{}{
    s =s10
    t =r5
    m = permission
    p = 4
    c = c7+c0+c6+c2+c9+c1+c8+c5
}
one sig rule3 extends Rule{}{
    s =s6
    t =r16
    m = prohibition
    p = 0
    c = c0+c8+c9+c7
}
one sig rule4 extends Rule{}{
    s =s10
    t =r7
    m = prohibition
    p = 1
    c = c7+c2+c5+c6+c9
}
one sig rule5 extends Rule{}{
    s =s15
    t =r6
    m = permission
    p = 4
    c = c1+c4+c5+c2+c3
}
one sig rule6 extends Rule{}{
    s =s5
    t =r15
    m = prohibition
    p = 3
    c = c5+c1+c2
}
one sig rule7 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 2
    c = c7
}
one sig rule8 extends Rule{}{
    s =s3
    t =r7
    m = permission
    p = 0
    c = c4+c5+c1
}
one sig rule9 extends Rule{}{
    s =s16
    t =r13
    m = permission
    p = 2
    c = c0+c6+c1+c2
}
one sig rule10 extends Rule{}{
    s =s10
    t =r8
    m = permission
    p = 4
    c = c8+c6+c3+c9+c1+c7+c4
}
one sig rule11 extends Rule{}{
    s =s9
    t =r1
    m = prohibition
    p = 2
    c = c2
}
one sig rule12 extends Rule{}{
    s =s10
    t =r14
    m = prohibition
    p = 2
    c = c8+c0+c5
}
one sig rule13 extends Rule{}{
    s =s16
    t =r13
    m = prohibition
    p = 0
    c = c4+c5+c6+c8
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

check ineffectiveRulerule13{ ineffectiveRule[rule13]}for 4

