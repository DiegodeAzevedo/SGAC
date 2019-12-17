module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s3+
         s7->s0+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s6+
         s9->s8+
         s10->s2+
         s10->s6+
         s10->s8+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s7+
         s12->s2+
         s12->s4+
         s12->s5+
         s13->s0+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s7+
         s15->s11+
         s15->s13+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s10+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r0+
         r4->r2+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r5+
         r8->r1+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r7+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r5+
         r14->r0+
         r14->r5+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r15->r0+
         r15->r2+
         r15->r4+
         r15->r9+
         r15->r10+
         r15->r11+
         r16->r3+
         r16->r9+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r13+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s3
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 0
    c = c6+c7+c2+c3+c1+c0
}
one sig rule1 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 3
    c = c0+c2+c8+c5+c3+c9+c6
}
one sig rule2 extends Rule{}{
    s =s6
    t =r12
    m = prohibition
    p = 1
    c = c4+c3+c6+c1
}
one sig rule3 extends Rule{}{
    s =s14
    t =r18
    m = permission
    p = 0
    c = c7+c4+c2
}
one sig rule4 extends Rule{}{
    s =s5
    t =r12
    m = permission
    p = 0
    c = c0+c8+c7+c1+c6
}
one sig rule5 extends Rule{}{
    s =s5
    t =r17
    m = prohibition
    p = 0
    c = c0+c5+c6+c3+c2
}
one sig rule6 extends Rule{}{
    s =s17
    t =r18
    m = permission
    p = 2
    c = c3
}
one sig rule7 extends Rule{}{
    s =s3
    t =r5
    m = permission
    p = 0
    c = c2+c3+c0+c7
}
one sig rule8 extends Rule{}{
    s =s13
    t =r13
    m = prohibition
    p = 3
    c = c2+c3+c4+c8+c5+c7+c6
}
one sig rule9 extends Rule{}{
    s =s17
    t =r4
    m = prohibition
    p = 1
    c = c1+c5+c6+c7+c8+c9
}
one sig rule10 extends Rule{}{
    s =s13
    t =r2
    m = permission
    p = 4
    c = c8+c5+c7+c9
}
one sig rule11 extends Rule{}{
    s =s5
    t =r10
    m = prohibition
    p = 1
    c = c6+c2+c4+c7+c0
}
one sig rule12 extends Rule{}{
    s =s19
    t =r14
    m = prohibition
    p = 2
    c = c8+c0+c4+c9+c6
}
one sig rule13 extends Rule{}{
    s =s17
    t =r7
    m = permission
    p = 3
    c = c8+c1+c4+c3+c2+c9
}
one sig rule14 extends Rule{}{
    s =s10
    t =r1
    m = permission
    p = 1
    c = c9+c4+c5+c8
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

