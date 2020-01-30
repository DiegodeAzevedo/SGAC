module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s4->s0+
         s4->s1+
         s4->s3+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s8->s1+
         s8->s4+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s3+
         s14->s5+
         s14->s9+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s11+
         s17->s12+
         s17->s13+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r0+
         r4->r0+
         r4->r3+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r2+
         r17->r7+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r18->r3+
         r18->r4+
         r18->r8+
         r18->r11+
         r18->r13+
         r18->r14+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r15+
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
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r1
    m = permission
    p = 3
    c = c9
}
one sig rule1 extends Rule{}{
    s =s1
    t =r18
    m = prohibition
    p = 4
    c = c6+c0+c4+c5+c3+c2
}
one sig rule2 extends Rule{}{
    s =s16
    t =r15
    m = permission
    p = 1
    c = c2+c4+c5+c9
}
one sig rule3 extends Rule{}{
    s =s12
    t =r1
    m = prohibition
    p = 1
    c = c1+c9+c3+c2
}
one sig rule4 extends Rule{}{
    s =s12
    t =r6
    m = prohibition
    p = 0
    c = c3+c1+c7+c2+c9+c6+c0
}
one sig rule5 extends Rule{}{
    s =s4
    t =r3
    m = permission
    p = 4
    c = c5+c1+c7+c8+c9+c4+c3
}
one sig rule6 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 3
    c = c5+c1+c2+c7
}
one sig rule7 extends Rule{}{
    s =s10
    t =r10
    m = prohibition
    p = 0
    c = c4+c3+c5+c1
}
one sig rule8 extends Rule{}{
    s =s6
    t =r16
    m = prohibition
    p = 4
    c = c1+c7+c3+c9
}
one sig rule9 extends Rule{}{
    s =s6
    t =r7
    m = permission
    p = 1
    c = c9+c4+c6+c5+c2
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

