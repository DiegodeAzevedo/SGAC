module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s2+
         s4->s1+
         s5->s0+
         s5->s1+
         s6->s1+
         s6->s2+
         s7->s1+
         s7->s2+
         s7->s3+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s6+
         s10->s8+
         s11->s4+
         s11->s5+
         s11->s9+
         s12->s0+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s10+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s7+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r5->r0+
         r5->r3+
         r6->r1+
         r6->r4+
         r7->r0+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r6+
         r9->r7+
         r10->r2+
         r10->r4+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r4+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r11+
         r15->r1+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r10+
         r16->r11+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r0+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r5+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 4
    c = c5+c6+c1+c4+c7
}
one sig rule1 extends Rule{}{
    s =s14
    t =r9
    m = permission
    p = 0
    c = c3+c8+c1+c5
}
one sig rule2 extends Rule{}{
    s =s10
    t =r0
    m = prohibition
    p = 2
    c = c0+c5
}
one sig rule3 extends Rule{}{
    s =s10
    t =r4
    m = prohibition
    p = 1
    c = c6+c7
}
one sig rule4 extends Rule{}{
    s =s16
    t =r6
    m = prohibition
    p = 2
    c = c6+c7+c3+c5
}
one sig rule5 extends Rule{}{
    s =s18
    t =r2
    m = prohibition
    p = 2
    c = c9+c2+c7+c4+c0
}
one sig rule6 extends Rule{}{
    s =s4
    t =r10
    m = prohibition
    p = 4
    c = c3+c6
}
one sig rule7 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 1
    c = c2+c0+c6
}
one sig rule8 extends Rule{}{
    s =s17
    t =r4
    m = prohibition
    p = 1
    c = c1+c2+c0+c4+c8+c9+c3
}
one sig rule9 extends Rule{}{
    s =s12
    t =r4
    m = permission
    p = 2
    c = c0+c9+c6+c2+c1+c5
}
one sig rule10 extends Rule{}{
    s =s18
    t =r2
    m = prohibition
    p = 2
    c = c1+c4+c2+c7
}
one sig rule11 extends Rule{}{
    s =s17
    t =r6
    m = prohibition
    p = 4
    c = c1+c2
}
one sig rule12 extends Rule{}{
    s =s15
    t =r12
    m = prohibition
    p = 2
    c = c1+c4+c2+c3+c0
}
one sig rule13 extends Rule{}{
    s =s16
    t =r10
    m = permission
    p = 3
    c = c3+c9+c2
}
one sig rule14 extends Rule{}{
    s =s0
    t =r14
    m = prohibition
    p = 1
    c = c9+c4+c2
}
one sig rule15 extends Rule{}{
    s =s19
    t =r7
    m = permission
    p = 4
    c = c2+c0
}
one sig rule16 extends Rule{}{
    s =s1
    t =r5
    m = permission
    p = 0
    c = c3+c4+c7+c0+c1+c5+c8
}
one sig rule17 extends Rule{}{
    s =s16
    t =r13
    m = permission
    p = 2
    c = c4+c5+c0
}
one sig rule18 extends Rule{}{
    s =s18
    t =r1
    m = permission
    p = 3
    c = c9+c0+c1+c6+c8
}
one sig rule19 extends Rule{}{
    s =s7
    t =r5
    m = permission
    p = 0
    c = c2+c0+c6+c7+c3
}
one sig rule20 extends Rule{}{
    s =s5
    t =r10
    m = permission
    p = 4
    c = c0+c3+c9+c1+c8
}
one sig rule21 extends Rule{}{
    s =s5
    t =r8
    m = permission
    p = 1
    c = c3+c9+c4+c7
}
one sig rule22 extends Rule{}{
    s =s4
    t =r5
    m = prohibition
    p = 3
    c = c9+c3+c4+c8+c1+c7+c2
}
one sig rule23 extends Rule{}{
    s =s0
    t =r3
    m = prohibition
    p = 2
    c = c2
}
one sig rule24 extends Rule{}{
    s =s14
    t =r4
    m = permission
    p = 2
    c = c1+c2+c5+c3+c6
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

check ineffectiveRulerule11{ ineffectiveRule[rule11]}for 4

check ineffectiveRulerule12{ ineffectiveRule[rule12]}for 4

check ineffectiveRulerule13{ ineffectiveRule[rule13]}for 4

check ineffectiveRulerule14{ ineffectiveRule[rule14]}for 4

check ineffectiveRulerule15{ ineffectiveRule[rule15]}for 4

check ineffectiveRulerule16{ ineffectiveRule[rule16]}for 4

check ineffectiveRulerule17{ ineffectiveRule[rule17]}for 4

check ineffectiveRulerule18{ ineffectiveRule[rule18]}for 4

check ineffectiveRulerule19{ ineffectiveRule[rule19]}for 4

check ineffectiveRulerule20{ ineffectiveRule[rule20]}for 4

check ineffectiveRulerule21{ ineffectiveRule[rule21]}for 4

check ineffectiveRulerule22{ ineffectiveRule[rule22]}for 4

check ineffectiveRulerule23{ ineffectiveRule[rule23]}for 4

check ineffectiveRulerule24{ ineffectiveRule[rule24]}for 4

