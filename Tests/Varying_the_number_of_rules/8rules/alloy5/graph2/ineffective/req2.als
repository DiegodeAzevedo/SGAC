module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s4+
         s6->s1+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s5+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s7+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s12+
         s17->s16+
         s18->s0+
         s18->s3+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s16+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r14->r0+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r12+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r11+
         r19->r13+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s3
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r3
    m = permission
    p = 1
    c = c6+c4+c7
}
one sig rule1 extends Rule{}{
    s =s4
    t =r4
    m = prohibition
    p = 3
    c = c5+c7
}
one sig rule2 extends Rule{}{
    s =s6
    t =r9
    m = permission
    p = 1
    c = c1+c2
}
one sig rule3 extends Rule{}{
    s =s12
    t =r1
    m = prohibition
    p = 3
    c = c8+c3+c5+c0+c7
}
one sig rule4 extends Rule{}{
    s =s19
    t =r6
    m = prohibition
    p = 4
    c = c7+c5
}
one sig rule5 extends Rule{}{
    s =s12
    t =r11
    m = prohibition
    p = 4
    c = c6+c9+c1
}
one sig rule6 extends Rule{}{
    s =s17
    t =r8
    m = prohibition
    p = 2
    c = c2+c5+c0+c1+c6+c3
}
one sig rule7 extends Rule{}{
    s =s14
    t =r4
    m = permission
    p = 2
    c = c6+c4+c8+c9
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

