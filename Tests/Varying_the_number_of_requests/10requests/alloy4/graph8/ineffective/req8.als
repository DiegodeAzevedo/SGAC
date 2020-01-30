module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s3+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s7+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s13->s1+
         s13->s3+
         s13->s6+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s16->s1+
         s16->s4+
         s16->s5+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s15+
         s17->s1+
         s17->s12+
         s18->s1+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s7+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r1+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r9+
         r16->r10+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r15+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req8 extends Request{}{
sub=s6
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r5
    m = permission
    p = 0
    c = c8+c4
}
one sig rule1 extends Rule{}{
    s =s5
    t =r19
    m = permission
    p = 3
    c = c9+c2+c0+c3+c1+c7
}
one sig rule2 extends Rule{}{
    s =s9
    t =r11
    m = permission
    p = 0
    c = c2+c8+c6+c1
}
one sig rule3 extends Rule{}{
    s =s18
    t =r10
    m = prohibition
    p = 4
    c = c9
}
one sig rule4 extends Rule{}{
    s =s4
    t =r18
    m = permission
    p = 0
    c = c4+c7+c0+c5+c8+c9
}
one sig rule5 extends Rule{}{
    s =s4
    t =r13
    m = permission
    p = 1
    c = c2+c0+c9+c7+c1
}
one sig rule6 extends Rule{}{
    s =s12
    t =r14
    m = permission
    p = 2
    c = c3+c6+c4+c2+c0
}
one sig rule7 extends Rule{}{
    s =s14
    t =r11
    m = permission
    p = 4
    c = c2+c8+c7+c4
}
one sig rule8 extends Rule{}{
    s =s4
    t =r18
    m = prohibition
    p = 2
    c = c0+c4+c7
}
one sig rule9 extends Rule{}{
    s =s13
    t =r17
    m = prohibition
    p = 0
    c = c2+c0+c1
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

