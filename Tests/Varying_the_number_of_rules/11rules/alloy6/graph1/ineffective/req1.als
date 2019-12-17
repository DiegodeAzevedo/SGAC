module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s2+
         s4->s1+
         s4->s3+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s7+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s7+
         s13->s1+
         s13->s4+
         s13->s6+
         s13->s10+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s1+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s8+
         s18->s12+
         s18->s15+
         s18->s16+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r1+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r4+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r7+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r12->r0+
         r12->r2+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r7+
         r18->r12+
         r18->r14+
         r18->r16+
         r19->r0+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r14+
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
    s =s10
    t =r6
    m = permission
    p = 2
    c = c7+c9+c3+c4
}
one sig rule1 extends Rule{}{
    s =s16
    t =r10
    m = permission
    p = 3
    c = c8
}
one sig rule2 extends Rule{}{
    s =s1
    t =r0
    m = permission
    p = 3
    c = c4
}
one sig rule3 extends Rule{}{
    s =s18
    t =r16
    m = prohibition
    p = 3
    c = c5+c8+c4+c2
}
one sig rule4 extends Rule{}{
    s =s11
    t =r6
    m = permission
    p = 4
    c = c5+c4+c9
}
one sig rule5 extends Rule{}{
    s =s16
    t =r10
    m = prohibition
    p = 0
    c = c6+c4+c7
}
one sig rule6 extends Rule{}{
    s =s18
    t =r17
    m = prohibition
    p = 0
    c = c3
}
one sig rule7 extends Rule{}{
    s =s4
    t =r12
    m = prohibition
    p = 1
    c = c2+c6+c4+c7+c5+c1
}
one sig rule8 extends Rule{}{
    s =s0
    t =r2
    m = prohibition
    p = 2
    c = c1+c2+c4
}
one sig rule9 extends Rule{}{
    s =s19
    t =r16
    m = permission
    p = 2
    c = c9+c3+c1+c2+c7
}
one sig rule10 extends Rule{}{
    s =s18
    t =r2
    m = prohibition
    p = 1
    c = c4+c8+c2+c9+c1+c6
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

