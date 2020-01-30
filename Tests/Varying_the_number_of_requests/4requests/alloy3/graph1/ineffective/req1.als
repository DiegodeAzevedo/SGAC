module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s1+
         s4->s2+
         s5->s1+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s3+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s3+
         s9->s5+
         s9->s7+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s1+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s4+
         s13->s8+
         s13->s9+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s4+
         s16->s7+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s10+
         s17->s11+
         s17->s12+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s11+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r8+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r8+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r9+
         r18->r13+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r8+
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
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r14
    m = prohibition
    p = 0
    c = c2+c5+c6+c3+c0
}
one sig rule1 extends Rule{}{
    s =s7
    t =r17
    m = permission
    p = 2
    c = c7+c4+c2+c5+c0+c6+c1+c9
}
one sig rule2 extends Rule{}{
    s =s0
    t =r13
    m = permission
    p = 1
    c = c3+c7+c5+c9+c0
}
one sig rule3 extends Rule{}{
    s =s10
    t =r1
    m = prohibition
    p = 0
    c = c1+c5+c3
}
one sig rule4 extends Rule{}{
    s =s10
    t =r13
    m = permission
    p = 1
    c = c4
}
one sig rule5 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 4
    c = c7
}
one sig rule6 extends Rule{}{
    s =s0
    t =r10
    m = permission
    p = 4
    c = c5
}
one sig rule7 extends Rule{}{
    s =s18
    t =r4
    m = prohibition
    p = 0
    c = c2+c9+c1+c6+c3+c0
}
one sig rule8 extends Rule{}{
    s =s7
    t =r1
    m = permission
    p = 1
    c = c0+c7+c2+c6
}
one sig rule9 extends Rule{}{
    s =s10
    t =r16
    m = prohibition
    p = 4
    c = c9+c4+c0
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

