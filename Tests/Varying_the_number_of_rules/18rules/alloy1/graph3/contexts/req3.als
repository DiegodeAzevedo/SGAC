module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s2+
         s11->s3+
         s12->s3+
         s12->s4+
         s12->s10+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s6+
         s15->s7+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s1+
         s18->s5+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r1+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r5+
         r7->r3+
         r7->r4+
         r8->r2+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r11+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r10+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r16+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s19
    t =r4
    m = permission
    p = 3
    c = c3+c1+c0+c2+c7+c4
}
one sig rule1 extends Rule{}{
    s =s15
    t =r18
    m = prohibition
    p = 1
    c = c7+c6
}
one sig rule2 extends Rule{}{
    s =s10
    t =r5
    m = permission
    p = 4
    c = c6+c3+c0+c5+c8
}
one sig rule3 extends Rule{}{
    s =s3
    t =r18
    m = prohibition
    p = 2
    c = c0+c8+c7+c1+c5
}
one sig rule4 extends Rule{}{
    s =s7
    t =r4
    m = prohibition
    p = 4
    c = c6+c8
}
one sig rule5 extends Rule{}{
    s =s14
    t =r13
    m = permission
    p = 0
    c = c8
}
one sig rule6 extends Rule{}{
    s =s3
    t =r9
    m = prohibition
    p = 3
    c = c6+c2+c0+c4+c3
}
one sig rule7 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 3
    c = c4+c2+c5+c8+c1+c7
}
one sig rule8 extends Rule{}{
    s =s10
    t =r3
    m = prohibition
    p = 3
    c = c5+c6+c3
}
one sig rule9 extends Rule{}{
    s =s1
    t =r19
    m = permission
    p = 0
    c = c8+c3+c2
}
one sig rule10 extends Rule{}{
    s =s18
    t =r9
    m = permission
    p = 4
    c = c3+c5+c9+c2+c7+c6
}
one sig rule11 extends Rule{}{
    s =s12
    t =r11
    m = prohibition
    p = 1
    c = c0+c5+c7
}
one sig rule12 extends Rule{}{
    s =s12
    t =r12
    m = permission
    p = 0
    c = c2+c0+c9
}
one sig rule13 extends Rule{}{
    s =s17
    t =r16
    m = permission
    p = 1
    c = c5+c9+c2+c0+c1+c7+c4
}
one sig rule14 extends Rule{}{
    s =s11
    t =r18
    m = prohibition
    p = 4
    c = c2+c8+c0+c4
}
one sig rule15 extends Rule{}{
    s =s16
    t =r9
    m = prohibition
    p = 4
    c = c1+c6+c0+c2+c9+c4
}
one sig rule16 extends Rule{}{
    s =s0
    t =r17
    m = prohibition
    p = 0
    c = c6+c9+c0+c8
}
one sig rule17 extends Rule{}{
    s =s4
    t =r16
    m = permission
    p = 2
    c = c5+c8
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
//***conditions (contexts)***
//***************************

one sig GrantingContext{
        acc: set Context
}{}

pred grantingContextDet[req:Request]{
        all c: Context | access_condition[req,c] <=> c in GrantingContext.acc
}
//*** determination command ***
run grantingContextDetermination{grantingContextDet[req3]} for 4 but 1 GrantingContext