module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s2+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s5+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s8+
         s11->s4+
         s11->s6+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s10+
         s13->s1+
         s13->s5+
         s13->s6+
         s13->s8+
         s14->s0+
         s14->s1+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s15->s0+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s13+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s8+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s20->s1+
         s20->s4+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s4+
         s21->s7+
         s21->s8+
         s21->s12+
         s21->s16+
         s21->s17+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s19+
         s22->s20}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r7->r0+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r10+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r4+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r14+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r4+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r10+
         r19->r12+
         r19->r14+
         r19->r16+
         r19->r17+
         r20->r3+
         r20->r5+
         r20->r8+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r18+
         r20->r19+
         r21->r4+
         r21->r7+
         r21->r10+
         r21->r13+
         r21->r15+
         r21->r17+
         r21->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s16
    t =r10
    m = permission
    p = 0
    c = c8+c4+c9+c0+c1+c7+c6+c2
}
one sig rule1 extends Rule{}{
    s =s2
    t =r16
    m = permission
    p = 2
    c = c7+c4+c9+c5
}
one sig rule2 extends Rule{}{
    s =s2
    t =r2
    m = permission
    p = 0
    c = c8+c1+c9+c5
}
one sig rule3 extends Rule{}{
    s =s21
    t =r20
    m = permission
    p = 1
    c = c4+c2+c8+c1+c5
}
one sig rule4 extends Rule{}{
    s =s6
    t =r20
    m = prohibition
    p = 2
    c = c6+c8
}
one sig rule5 extends Rule{}{
    s =s9
    t =r15
    m = prohibition
    p = 4
    c = c7+c8+c2+c1+c9+c5
}
one sig rule6 extends Rule{}{
    s =s15
    t =r10
    m = permission
    p = 2
    c = c3+c8+c1+c2
}
one sig rule7 extends Rule{}{
    s =s19
    t =r17
    m = prohibition
    p = 4
    c = c3+c0+c1+c4+c2
}
one sig rule8 extends Rule{}{
    s =s4
    t =r20
    m = prohibition
    p = 1
    c = c9+c3+c5
}
one sig rule9 extends Rule{}{
    s =s8
    t =r9
    m = prohibition
    p = 1
    c = c8+c0+c2+c9+c6+c5+c7+c4
}
one sig rule10 extends Rule{}{
    s =s2
    t =r15
    m = prohibition
    p = 1
    c = c4+c9+c1+c8
}
one sig rule11 extends Rule{}{
    s =s12
    t =r16
    m = prohibition
    p = 3
    c = c3+c7+c1+c5+c2
}
one sig rule12 extends Rule{}{
    s =s14
    t =r11
    m = permission
    p = 4
    c = c3+c9
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

