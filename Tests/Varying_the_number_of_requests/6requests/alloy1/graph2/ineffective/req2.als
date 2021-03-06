module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s4+
         s13->s8+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s7+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s12+
         s18->s13+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r3+
         r7->r4+
         r8->r2+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r3+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r4+
         r11->r8+
         r12->r0+
         r12->r7+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r3+
         r14->r5+
         r14->r10+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r9+
         r15->r10+
         r15->r11+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r13+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r12+
         r19->r0+
         r19->r1+
         r19->r5+
         r19->r6+
         r19->r12}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r9
    m = permission
    p = 1
    c = c0+c4+c6+c3+c2+c7+c1
}
one sig rule1 extends Rule{}{
    s =s1
    t =r19
    m = prohibition
    p = 0
    c = c4+c7+c5+c3
}
one sig rule2 extends Rule{}{
    s =s15
    t =r13
    m = prohibition
    p = 4
    c = c1+c3+c4+c8+c5
}
one sig rule3 extends Rule{}{
    s =s4
    t =r15
    m = prohibition
    p = 4
    c = c8+c3+c2+c6+c4
}
one sig rule4 extends Rule{}{
    s =s18
    t =r4
    m = prohibition
    p = 2
    c = c2+c5+c8
}
one sig rule5 extends Rule{}{
    s =s1
    t =r15
    m = permission
    p = 3
    c = c5
}
one sig rule6 extends Rule{}{
    s =s19
    t =r0
    m = permission
    p = 2
    c = c4
}
one sig rule7 extends Rule{}{
    s =s19
    t =r11
    m = permission
    p = 2
    c = c0+c9+c1+c5+c6+c3
}
one sig rule8 extends Rule{}{
    s =s10
    t =r19
    m = permission
    p = 2
    c = c6+c5+c0+c8
}
one sig rule9 extends Rule{}{
    s =s11
    t =r5
    m = prohibition
    p = 0
    c = c8+c0
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

