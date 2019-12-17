module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s7+
         s9->s1+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s5+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s0+
         s12->s3+
         s12->s4+
         s12->s8+
         s12->s9+
         s13->s1+
         s13->s4+
         s13->s7+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s9+
         s15->s10+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s12+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s6+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r5->r1+
         r5->r3+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r6+
         r8->r0+
         r8->r4+
         r8->r6+
         r9->r1+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r8+
         r11->r1+
         r11->r4+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r9+
         r12->r11+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r10+
         r15->r12+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r7+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r12+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r11+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r7+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r15}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s12
    t =r7
    m = permission
    p = 3
    c = c1+c8+c3+c4+c9
}
one sig rule1 extends Rule{}{
    s =s0
    t =r2
    m = permission
    p = 4
    c = c7+c9+c1
}
one sig rule2 extends Rule{}{
    s =s4
    t =r11
    m = permission
    p = 4
    c = c1+c9+c8+c0+c5+c6
}
one sig rule3 extends Rule{}{
    s =s10
    t =r6
    m = prohibition
    p = 0
    c = c7+c2+c6
}
one sig rule4 extends Rule{}{
    s =s0
    t =r3
    m = permission
    p = 0
    c = c2+c0+c1+c3
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

