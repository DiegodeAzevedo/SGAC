module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s9->s0+
         s9->s1+
         s9->s5+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s8+
         s12->s10+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s11+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s9+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s14+
         s18->s2+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r4->r2+
         r5->r2+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r5+
         r9->r0+
         r9->r2+
         r10->r0+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r3+
         r11->r5+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r4+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r6+
         r13->r10+
         r13->r12+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r12+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r12+
         r17->r0+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
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
one sig req3 extends Request{}{
sub=s4
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r15
    m = prohibition
    p = 4
    c = c0+c4+c1+c2+c3
}
one sig rule1 extends Rule{}{
    s =s3
    t =r15
    m = permission
    p = 3
    c = c6+c7+c4+c8+c3+c0
}
one sig rule2 extends Rule{}{
    s =s11
    t =r0
    m = permission
    p = 1
    c = c0
}
one sig rule3 extends Rule{}{
    s =s14
    t =r10
    m = prohibition
    p = 2
    c = c3+c5+c1+c4+c9
}
one sig rule4 extends Rule{}{
    s =s15
    t =r18
    m = prohibition
    p = 4
    c = c1+c0+c5+c2+c8+c9
}
one sig rule5 extends Rule{}{
    s =s16
    t =r11
    m = prohibition
    p = 3
    c = c7
}
one sig rule6 extends Rule{}{
    s =s9
    t =r5
    m = prohibition
    p = 4
    c = c3+c4+c9+c0
}
one sig rule7 extends Rule{}{
    s =s8
    t =r4
    m = permission
    p = 4
    c = c7+c4+c6+c0+c5+c3
}
one sig rule8 extends Rule{}{
    s =s17
    t =r6
    m = prohibition
    p = 3
    c = c4
}
one sig rule9 extends Rule{}{
    s =s6
    t =r3
    m = prohibition
    p = 2
    c = c3
}
one sig rule10 extends Rule{}{
    s =s18
    t =r13
    m = prohibition
    p = 3
    c = c1+c7+c5+c0
}
one sig rule11 extends Rule{}{
    s =s12
    t =r6
    m = prohibition
    p = 4
    c = c2+c3+c4+c9+c8
}
one sig rule12 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 0
    c = c9+c6+c1+c2+c4+c3
}
one sig rule13 extends Rule{}{
    s =s7
    t =r12
    m = prohibition
    p = 3
    c = c3+c1
}
one sig rule14 extends Rule{}{
    s =s6
    t =r3
    m = prohibition
    p = 0
    c = c7+c6+c1+c5+c0+c2+c8+c3
}
one sig rule15 extends Rule{}{
    s =s14
    t =r17
    m = prohibition
    p = 3
    c = c9+c8+c4
}
one sig rule16 extends Rule{}{
    s =s3
    t =r17
    m = prohibition
    p = 2
    c = c5+c9+c0+c8
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

check ineffectiveRulerule14{ ineffectiveRule[rule14]}for 4

check ineffectiveRulerule15{ ineffectiveRule[rule15]}for 4

check ineffectiveRulerule16{ ineffectiveRule[rule16]}for 4

