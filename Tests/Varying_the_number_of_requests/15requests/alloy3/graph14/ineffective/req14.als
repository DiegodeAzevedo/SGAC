module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s2+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s11->s1+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s5+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s14+
         s16->s15+
         s17->s4+
         s17->s8+
         s17->s12+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s7+
         s18->s10+
         s18->s15+
         s19->s0+
         s19->s2+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r4->r1+
         r4->r3+
         r5->r3+
         r7->r1+
         r7->r3+
         r8->r1+
         r8->r3+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r9+
         r13->r10+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r3+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r12+
         r19->r14+
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
one sig req14 extends Request{}{
sub=s2
res=r6
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r4
    m = prohibition
    p = 1
    c = c3+c9+c6+c8+c2+c5
}
one sig rule1 extends Rule{}{
    s =s9
    t =r4
    m = prohibition
    p = 1
    c = c5+c8+c9+c4+c3
}
one sig rule2 extends Rule{}{
    s =s19
    t =r7
    m = prohibition
    p = 4
    c = c9
}
one sig rule3 extends Rule{}{
    s =s10
    t =r12
    m = prohibition
    p = 1
    c = c0+c4+c8+c9+c3
}
one sig rule4 extends Rule{}{
    s =s14
    t =r9
    m = permission
    p = 4
    c = c9+c5
}
one sig rule5 extends Rule{}{
    s =s3
    t =r0
    m = permission
    p = 1
    c = c4+c5+c3+c2+c8+c1+c0+c7
}
one sig rule6 extends Rule{}{
    s =s0
    t =r14
    m = permission
    p = 2
    c = c3+c7+c1+c0+c9
}
one sig rule7 extends Rule{}{
    s =s1
    t =r1
    m = prohibition
    p = 1
    c = c8
}
one sig rule8 extends Rule{}{
    s =s5
    t =r0
    m = permission
    p = 3
    c = c2+c5+c7+c0+c3
}
one sig rule9 extends Rule{}{
    s =s17
    t =r9
    m = permission
    p = 1
    c = c5+c9+c3+c4
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

