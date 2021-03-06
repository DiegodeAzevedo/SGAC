module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s10->s0+
         s10->s1+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s3+
         s12->s8+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s10+
         s15->s12+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s13+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r4->r0+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r9->r2+
         r9->r8+
         r10->r1+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r4+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r7+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r7+
         r14->r10+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r11+
         r17->r15+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r16+
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
    s =s3
    t =r10
    m = prohibition
    p = 1
    c = c9+c3+c8+c1+c6+c7+c0+c4
}
one sig rule1 extends Rule{}{
    s =s13
    t =r18
    m = prohibition
    p = 1
    c = c4+c2+c7+c8+c3+c1
}
one sig rule2 extends Rule{}{
    s =s13
    t =r10
    m = prohibition
    p = 0
    c = c5+c7+c1+c4
}
one sig rule3 extends Rule{}{
    s =s6
    t =r4
    m = prohibition
    p = 2
    c = c8
}
one sig rule4 extends Rule{}{
    s =s4
    t =r9
    m = prohibition
    p = 4
    c = c6+c8+c0+c5+c9+c4+c2
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

