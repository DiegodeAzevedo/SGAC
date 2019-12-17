module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
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
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s5+
         s7->s0+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s3+
         s14->s5+
         s14->s12+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s13+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r7+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r15->r0+
         r15->r2+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r14+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r11+
         r17->r1+
         r17->r2+
         r17->r8+
         r17->r11+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
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
    s =s11
    t =r16
    m = prohibition
    p = 4
    c = c9+c0+c2+c3
}
one sig rule1 extends Rule{}{
    s =s6
    t =r19
    m = permission
    p = 1
    c = c2+c5+c6+c0
}
one sig rule2 extends Rule{}{
    s =s2
    t =r13
    m = prohibition
    p = 0
    c = c2+c7+c1
}
one sig rule3 extends Rule{}{
    s =s15
    t =r12
    m = permission
    p = 4
    c = c5+c2+c4+c1+c6
}
one sig rule4 extends Rule{}{
    s =s1
    t =r18
    m = permission
    p = 1
    c = c9+c1+c7+c3
}
one sig rule5 extends Rule{}{
    s =s15
    t =r6
    m = permission
    p = 4
    c = c3
}
one sig rule6 extends Rule{}{
    s =s8
    t =r9
    m = permission
    p = 2
    c = c7+c8+c3+c0+c2
}
one sig rule7 extends Rule{}{
    s =s18
    t =r9
    m = permission
    p = 3
    c = c6+c1+c0+c9+c5+c8+c7
}
one sig rule8 extends Rule{}{
    s =s10
    t =r1
    m = prohibition
    p = 4
    c = c1+c3+c2+c5+c8+c7
}
one sig rule9 extends Rule{}{
    s =s4
    t =r11
    m = permission
    p = 4
    c = c6+c2+c0
}
one sig rule10 extends Rule{}{
    s =s9
    t =r4
    m = prohibition
    p = 4
    c = c3+c2+c5
}
one sig rule11 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 2
    c = c3+c2+c0+c6
}
one sig rule12 extends Rule{}{
    s =s4
    t =r5
    m = prohibition
    p = 0
    c = c3+c2+c6+c5+c9
}
one sig rule13 extends Rule{}{
    s =s17
    t =r10
    m = prohibition
    p = 3
    c = c4+c8+c1
}
one sig rule14 extends Rule{}{
    s =s13
    t =r3
    m = prohibition
    p = 3
    c = c3+c2+c0
}
one sig rule15 extends Rule{}{
    s =s13
    t =r14
    m = prohibition
    p = 0
    c = c8+c1+c9+c5
}
one sig rule16 extends Rule{}{
    s =s18
    t =r5
    m = prohibition
    p = 0
    c = c9+c0+c4+c3
}
one sig rule17 extends Rule{}{
    s =s14
    t =r15
    m = permission
    p = 0
    c = c5+c9+c2+c7+c4+c8+c0
}
one sig rule18 extends Rule{}{
    s =s7
    t =r2
    m = prohibition
    p = 2
    c = c4
}
one sig rule19 extends Rule{}{
    s =s14
    t =r3
    m = prohibition
    p = 4
    c = c6+c9+c7+c2+c3+c0+c5
}
one sig rule20 extends Rule{}{
    s =s1
    t =r14
    m = permission
    p = 3
    c = c5+c2+c8+c6+c4+c1+c7
}
one sig rule21 extends Rule{}{
    s =s2
    t =r5
    m = permission
    p = 1
    c = c4+c9+c7+c2+c3
}
one sig rule22 extends Rule{}{
    s =s12
    t =r10
    m = prohibition
    p = 0
    c = c3+c1+c0+c7+c8+c5
}
one sig rule23 extends Rule{}{
    s =s9
    t =r3
    m = permission
    p = 1
    c = c2+c1+c4+c7+c5
}
one sig rule24 extends Rule{}{
    s =s13
    t =r6
    m = prohibition
    p = 4
    c = c8
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
run grantingContextDetermination{grantingContextDet[req0]} for 4 but 1 GrantingContext