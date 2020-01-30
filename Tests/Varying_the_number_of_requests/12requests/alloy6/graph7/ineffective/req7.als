module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s6->s4+
         s7->s1+
         s7->s5+
         s8->s0+
         s8->s3+
         s8->s5+
         s9->s2+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s8+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s6+
         s12->s9+
         s12->s10+
         s13->s2+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s8+
         s14->s11+
         s15->s0+
         s15->s2+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s12+
         s17->s13+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s6+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r1+
         r4->r0+
         r4->r2+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r8+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r8+
         r14->r9+
         r14->r12+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r8+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r13+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r3+
         r18->r6+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r13+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
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
one sig req7 extends Request{}{
sub=s4
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r12
    m = permission
    p = 3
    c = c1+c4+c9+c2
}
one sig rule1 extends Rule{}{
    s =s7
    t =r17
    m = prohibition
    p = 0
    c = c2+c0+c9+c1
}
one sig rule2 extends Rule{}{
    s =s18
    t =r0
    m = permission
    p = 0
    c = c3
}
one sig rule3 extends Rule{}{
    s =s13
    t =r0
    m = permission
    p = 2
    c = c3+c4+c6+c0+c5+c7+c1+c9
}
one sig rule4 extends Rule{}{
    s =s7
    t =r10
    m = prohibition
    p = 4
    c = c8+c1+c7+c3
}
one sig rule5 extends Rule{}{
    s =s1
    t =r7
    m = permission
    p = 2
    c = c5+c4
}
one sig rule6 extends Rule{}{
    s =s10
    t =r5
    m = permission
    p = 0
    c = c9+c5+c6+c7+c4
}
one sig rule7 extends Rule{}{
    s =s3
    t =r11
    m = permission
    p = 2
    c = c7+c4+c9
}
one sig rule8 extends Rule{}{
    s =s5
    t =r12
    m = permission
    p = 2
    c = c0
}
one sig rule9 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 3
    c = c3+c1+c4+c5
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

