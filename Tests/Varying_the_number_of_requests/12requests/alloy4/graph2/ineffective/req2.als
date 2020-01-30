module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s5+
         s9->s2+
         s9->s6+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s7+
         s11->s2+
         s11->s5+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s10+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s6+
         s16->s12+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s6+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r6+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r10+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r3
    m = prohibition
    p = 2
    c = c9
}
one sig rule1 extends Rule{}{
    s =s15
    t =r15
    m = prohibition
    p = 4
    c = c2+c9+c1+c6+c5
}
one sig rule2 extends Rule{}{
    s =s4
    t =r0
    m = permission
    p = 1
    c = c0+c9+c7+c4
}
one sig rule3 extends Rule{}{
    s =s13
    t =r4
    m = permission
    p = 1
    c = c1+c3+c2
}
one sig rule4 extends Rule{}{
    s =s19
    t =r8
    m = prohibition
    p = 1
    c = c4+c9+c0+c6+c1+c2
}
one sig rule5 extends Rule{}{
    s =s1
    t =r9
    m = permission
    p = 0
    c = c0+c1
}
one sig rule6 extends Rule{}{
    s =s19
    t =r5
    m = prohibition
    p = 0
    c = c2+c7+c5+c8
}
one sig rule7 extends Rule{}{
    s =s5
    t =r1
    m = permission
    p = 1
    c = c5+c7+c8+c9+c4+c3
}
one sig rule8 extends Rule{}{
    s =s11
    t =r5
    m = prohibition
    p = 3
    c = c6+c1+c0+c7+c2+c9
}
one sig rule9 extends Rule{}{
    s =s13
    t =r3
    m = prohibition
    p = 4
    c = c1+c5+c7+c4+c0+c2
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

