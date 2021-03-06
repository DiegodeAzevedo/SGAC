module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s4->s1+
         s4->s2+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s4+
         s7->s1+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s5+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s6+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s15+
         s18->s3+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s11+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r1+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r2+
         r7->r6+
         r8->r0+
         r8->r2+
         r9->r0+
         r9->r3+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r5+
         r12->r5+
         r12->r8+
         r12->r9+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r10+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r10+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r10+
         r18->r12+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r15+
         r19->r16+
         r19->r17}

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
    s =s7
    t =r16
    m = permission
    p = 4
    c = c7+c5+c3+c0
}
one sig rule1 extends Rule{}{
    s =s6
    t =r13
    m = permission
    p = 2
    c = c6+c0+c4+c3+c2
}
one sig rule2 extends Rule{}{
    s =s1
    t =r3
    m = prohibition
    p = 3
    c = c0+c5+c7+c2
}
one sig rule3 extends Rule{}{
    s =s18
    t =r2
    m = permission
    p = 4
    c = c8+c5
}
one sig rule4 extends Rule{}{
    s =s11
    t =r14
    m = prohibition
    p = 1
    c = c9+c1+c8+c4+c3+c5+c2
}
one sig rule5 extends Rule{}{
    s =s13
    t =r15
    m = permission
    p = 2
    c = c6
}
one sig rule6 extends Rule{}{
    s =s9
    t =r1
    m = permission
    p = 1
    c = c3+c6+c9+c2+c0
}
one sig rule7 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 2
    c = c0+c3
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

