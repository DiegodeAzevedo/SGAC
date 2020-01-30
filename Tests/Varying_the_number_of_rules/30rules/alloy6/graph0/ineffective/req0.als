module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s1+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s9->s0+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s3+
         s10->s7+
         s10->s8+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s12+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s5+
         s15->s6+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s13+
         s16->s1+
         s16->s5+
         s16->s7+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s13+
         s19->s15+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r5->r0+
         r5->r1+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r5+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r10+
         r13->r0+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r14->r2+
         r14->r4+
         r14->r9+
         r14->r12+
         r15->r0+
         r15->r3+
         r15->r6+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
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
    s =s9
    t =r19
    m = prohibition
    p = 4
    c = c8+c5+c7+c0
}
one sig rule1 extends Rule{}{
    s =s14
    t =r14
    m = prohibition
    p = 1
    c = c3+c7+c5+c9
}
one sig rule2 extends Rule{}{
    s =s7
    t =r3
    m = permission
    p = 2
    c = c3+c5+c4+c8
}
one sig rule3 extends Rule{}{
    s =s7
    t =r0
    m = prohibition
    p = 0
    c = c8
}
one sig rule4 extends Rule{}{
    s =s12
    t =r14
    m = permission
    p = 2
    c = c8+c6+c5+c9+c3+c7
}
one sig rule5 extends Rule{}{
    s =s4
    t =r3
    m = permission
    p = 3
    c = c8+c1+c6+c3+c2+c9
}
one sig rule6 extends Rule{}{
    s =s16
    t =r0
    m = prohibition
    p = 2
    c = c4+c2
}
one sig rule7 extends Rule{}{
    s =s16
    t =r8
    m = permission
    p = 4
    c = c3+c0
}
one sig rule8 extends Rule{}{
    s =s16
    t =r14
    m = permission
    p = 3
    c = c2
}
one sig rule9 extends Rule{}{
    s =s0
    t =r12
    m = permission
    p = 0
    c = c6+c1+c8+c7+c3+c0
}
one sig rule10 extends Rule{}{
    s =s11
    t =r0
    m = permission
    p = 4
    c = c6+c7+c2+c0
}
one sig rule11 extends Rule{}{
    s =s13
    t =r16
    m = prohibition
    p = 0
    c = c6+c7+c2+c0+c9+c4
}
one sig rule12 extends Rule{}{
    s =s18
    t =r7
    m = prohibition
    p = 4
    c = c4+c6+c7+c2+c1
}
one sig rule13 extends Rule{}{
    s =s13
    t =r15
    m = prohibition
    p = 1
    c = c3
}
one sig rule14 extends Rule{}{
    s =s6
    t =r2
    m = permission
    p = 1
    c = c0+c3
}
one sig rule15 extends Rule{}{
    s =s15
    t =r4
    m = prohibition
    p = 0
    c = c4+c7+c6+c5+c2
}
one sig rule16 extends Rule{}{
    s =s5
    t =r7
    m = prohibition
    p = 1
    c = c0+c8+c5+c2+c9+c1+c3
}
one sig rule17 extends Rule{}{
    s =s15
    t =r19
    m = permission
    p = 0
    c = c8
}
one sig rule18 extends Rule{}{
    s =s3
    t =r19
    m = permission
    p = 0
    c = c7+c8
}
one sig rule19 extends Rule{}{
    s =s8
    t =r9
    m = prohibition
    p = 4
    c = c4+c7+c5+c1+c3+c8
}
one sig rule20 extends Rule{}{
    s =s5
    t =r8
    m = prohibition
    p = 3
    c = c4+c1+c0+c2+c6
}
one sig rule21 extends Rule{}{
    s =s1
    t =r5
    m = permission
    p = 0
    c = c1+c6+c3+c7+c9
}
one sig rule22 extends Rule{}{
    s =s16
    t =r19
    m = prohibition
    p = 2
    c = c8+c5
}
one sig rule23 extends Rule{}{
    s =s7
    t =r10
    m = permission
    p = 0
    c = c4+c1+c8+c5
}
one sig rule24 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 1
    c = c6
}
one sig rule25 extends Rule{}{
    s =s3
    t =r8
    m = prohibition
    p = 0
    c = c4+c6+c2
}
one sig rule26 extends Rule{}{
    s =s18
    t =r0
    m = permission
    p = 4
    c = c5+c0+c8+c7
}
one sig rule27 extends Rule{}{
    s =s15
    t =r5
    m = permission
    p = 0
    c = c8+c1+c5+c0
}
one sig rule28 extends Rule{}{
    s =s4
    t =r10
    m = prohibition
    p = 0
    c = c7+c1+c2+c6+c8
}
one sig rule29 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 4
    c = c4+c0
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

check ineffectiveRulerule25{ ineffectiveRule[rule25]}for 4

check ineffectiveRulerule26{ ineffectiveRule[rule26]}for 4

check ineffectiveRulerule27{ ineffectiveRule[rule27]}for 4

check ineffectiveRulerule28{ ineffectiveRule[rule28]}for 4

check ineffectiveRulerule29{ ineffectiveRule[rule29]}for 4

