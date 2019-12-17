module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s4+
         s9->s7+
         s10->s1+
         s10->s4+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s4+
         s11->s5+
         s11->s7+
         s12->s3+
         s12->s4+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s8+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s5+
         s16->s10+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s5+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r5+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r6+
         r11->r7+
         r12->r0+
         r12->r7+
         r12->r9+
         r12->r10+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r7+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r3+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r15+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r9
    m = permission
    p = 4
    c = c7+c1
}
one sig rule1 extends Rule{}{
    s =s6
    t =r18
    m = prohibition
    p = 2
    c = c0+c5+c9+c8+c6
}
one sig rule2 extends Rule{}{
    s =s7
    t =r16
    m = permission
    p = 4
    c = c8+c9+c5+c2+c0+c3
}
one sig rule3 extends Rule{}{
    s =s17
    t =r6
    m = permission
    p = 1
    c = c6+c9+c7+c4+c0
}
one sig rule4 extends Rule{}{
    s =s12
    t =r12
    m = prohibition
    p = 1
    c = c7+c1+c9+c3+c0+c5
}
one sig rule5 extends Rule{}{
    s =s6
    t =r14
    m = permission
    p = 0
    c = c8+c7
}
one sig rule6 extends Rule{}{
    s =s6
    t =r14
    m = prohibition
    p = 4
    c = c0+c1+c3+c8
}
one sig rule7 extends Rule{}{
    s =s3
    t =r4
    m = permission
    p = 3
    c = c2+c0+c6
}
one sig rule8 extends Rule{}{
    s =s10
    t =r10
    m = permission
    p = 3
    c = c5+c6+c3+c0+c8
}
one sig rule9 extends Rule{}{
    s =s17
    t =r17
    m = prohibition
    p = 3
    c = c3+c4+c1+c6+c0
}
one sig rule10 extends Rule{}{
    s =s8
    t =r12
    m = permission
    p = 1
    c = c8+c7+c0+c4+c9+c3
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

