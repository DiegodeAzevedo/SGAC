module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s2+
         s4->s3+
         s5->s2+
         s5->s4+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s2+
         s10->s4+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s14+
         s17->s0+
         s17->s3+
         s17->s7+
         s17->s10+
         s17->s12+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s10+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r6->r1+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r8+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r7+
         r15->r8+
         r15->r12+
         r16->r0+
         r16->r10+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r10+
         r18->r14+
         r19->r2+
         r19->r3+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r17+
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
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r7
    m = permission
    p = 4
    c = c1+c0+c4+c6+c8+c3+c5
}
one sig rule1 extends Rule{}{
    s =s5
    t =r17
    m = prohibition
    p = 0
    c = c3
}
one sig rule2 extends Rule{}{
    s =s8
    t =r1
    m = prohibition
    p = 4
    c = c6+c9+c7
}
one sig rule3 extends Rule{}{
    s =s6
    t =r4
    m = permission
    p = 1
    c = c5+c4
}
one sig rule4 extends Rule{}{
    s =s16
    t =r15
    m = permission
    p = 0
    c = c3+c1+c7+c0+c5+c4+c8
}
one sig rule5 extends Rule{}{
    s =s16
    t =r13
    m = prohibition
    p = 0
    c = c1+c2+c3+c6
}
one sig rule6 extends Rule{}{
    s =s11
    t =r8
    m = prohibition
    p = 2
    c = c5+c0
}
one sig rule7 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 3
    c = c0
}
one sig rule8 extends Rule{}{
    s =s2
    t =r2
    m = prohibition
    p = 2
    c = c7+c4
}
one sig rule9 extends Rule{}{
    s =s16
    t =r1
    m = permission
    p = 1
    c = c5+c8+c0+c1
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

