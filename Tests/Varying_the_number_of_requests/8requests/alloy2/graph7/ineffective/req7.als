module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s4+
         s6->s0+
         s6->s4+
         s6->s5+
         s7->s4+
         s7->s5+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s5+
         s9->s6+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s7+
         s11->s2+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s10+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s13+
         s15->s5+
         s15->s6+
         s15->s9+
         s15->s10+
         s15->s12+
         s16->s3+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s12+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s3+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s14}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r3+
         r6->r1+
         r6->r3+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r9+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r5+
         r13->r7+
         r13->r12+
         r14->r0+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r1+
         r17->r2+
         r17->r6+
         r17->r9+
         r17->r11+
         r17->r12+
         r18->r2+
         r18->r3+
         r18->r8+
         r18->r9+
         r18->r12+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r7+
         r19->r9+
         r19->r11+
         r19->r14+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req7 extends Request{}{
sub=s3
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s16
    t =r9
    m = prohibition
    p = 4
    c = c8+c4+c9
}
one sig rule1 extends Rule{}{
    s =s5
    t =r0
    m = prohibition
    p = 2
    c = c8+c0
}
one sig rule2 extends Rule{}{
    s =s10
    t =r1
    m = prohibition
    p = 3
    c = c5+c3+c8+c7+c2
}
one sig rule3 extends Rule{}{
    s =s13
    t =r10
    m = permission
    p = 4
    c = c2+c8
}
one sig rule4 extends Rule{}{
    s =s8
    t =r13
    m = permission
    p = 4
    c = c8+c2+c6+c0
}
one sig rule5 extends Rule{}{
    s =s8
    t =r4
    m = permission
    p = 3
    c = c3+c8+c5+c7+c1+c0+c4
}
one sig rule6 extends Rule{}{
    s =s12
    t =r11
    m = permission
    p = 1
    c = c3
}
one sig rule7 extends Rule{}{
    s =s0
    t =r13
    m = prohibition
    p = 2
    c = c2
}
one sig rule8 extends Rule{}{
    s =s3
    t =r6
    m = prohibition
    p = 0
    c = c0+c3+c5+c2+c8
}
one sig rule9 extends Rule{}{
    s =s8
    t =r12
    m = prohibition
    p = 2
    c = c3+c4+c5+c2
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

