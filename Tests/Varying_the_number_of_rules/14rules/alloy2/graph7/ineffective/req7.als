module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s4+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s9->s2+
         s9->s4+
         s9->s7+
         s10->s2+
         s10->s4+
         s10->s6+
         s11->s0+
         s11->s1+
         s11->s6+
         s11->s7+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s7+
         s12->s10+
         s13->s0+
         s13->s4+
         s13->s6+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s14+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s17->s0+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s12+
         s18->s16+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r4->r2+
         r4->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r3+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r3+
         r9->r6+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r7+
         r10->r9+
         r11->r3+
         r11->r4+
         r11->r8+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r8+
         r13->r0+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r11+
         r16->r12+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r16+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req7 extends Request{}{
sub=s3
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 2
    c = c4+c6+c3+c5+c8
}
one sig rule1 extends Rule{}{
    s =s13
    t =r16
    m = prohibition
    p = 4
    c = c3+c5+c6+c2+c4+c9+c7
}
one sig rule2 extends Rule{}{
    s =s14
    t =r10
    m = prohibition
    p = 0
    c = c9+c5+c1
}
one sig rule3 extends Rule{}{
    s =s8
    t =r10
    m = permission
    p = 3
    c = c1+c3+c5+c8+c2+c9+c4
}
one sig rule4 extends Rule{}{
    s =s18
    t =r5
    m = prohibition
    p = 2
    c = c4+c1
}
one sig rule5 extends Rule{}{
    s =s10
    t =r15
    m = permission
    p = 3
    c = c2+c4+c5
}
one sig rule6 extends Rule{}{
    s =s14
    t =r18
    m = prohibition
    p = 2
    c = c3+c4+c9+c5+c8
}
one sig rule7 extends Rule{}{
    s =s4
    t =r3
    m = prohibition
    p = 2
    c = c0+c5+c7+c9+c6
}
one sig rule8 extends Rule{}{
    s =s14
    t =r15
    m = permission
    p = 4
    c = c2+c7+c6+c4+c1+c5
}
one sig rule9 extends Rule{}{
    s =s14
    t =r11
    m = permission
    p = 1
    c = c8+c1+c4
}
one sig rule10 extends Rule{}{
    s =s18
    t =r17
    m = permission
    p = 4
    c = c9+c5+c3+c2
}
one sig rule11 extends Rule{}{
    s =s4
    t =r15
    m = permission
    p = 3
    c = c5+c4+c9
}
one sig rule12 extends Rule{}{
    s =s1
    t =r15
    m = prohibition
    p = 0
    c = c3+c2+c9+c5+c8+c1+c7+c6
}
one sig rule13 extends Rule{}{
    s =s14
    t =r9
    m = prohibition
    p = 2
    c = c2+c3+c1+c6+c9
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

