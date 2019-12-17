module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s6->s0+
         s6->s3+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s10+
         s12->s5+
         s12->s6+
         s12->s8+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s8+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s11+
         s16->s2+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s12+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s7+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r4->r1+
         r5->r0+
         r5->r2+
         r6->r2+
         r6->r3+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r3+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r5+
         r13->r7+
         r13->r11+
         r13->r12+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r7+
         r15->r9+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r11+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r17+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r14+
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
    s =s17
    t =r4
    m = prohibition
    p = 2
    c = c7+c3+c2+c6+c8+c0
}
one sig rule1 extends Rule{}{
    s =s10
    t =r10
    m = permission
    p = 2
    c = c2+c8+c1+c0
}
one sig rule2 extends Rule{}{
    s =s9
    t =r6
    m = prohibition
    p = 2
    c = c6
}
one sig rule3 extends Rule{}{
    s =s7
    t =r0
    m = prohibition
    p = 3
    c = c4+c7+c9+c2+c1+c0
}
one sig rule4 extends Rule{}{
    s =s18
    t =r11
    m = prohibition
    p = 0
    c = c4
}
one sig rule5 extends Rule{}{
    s =s7
    t =r14
    m = permission
    p = 3
    c = c9+c1+c8+c5
}
one sig rule6 extends Rule{}{
    s =s19
    t =r4
    m = prohibition
    p = 3
    c = c3+c8+c5
}
one sig rule7 extends Rule{}{
    s =s16
    t =r3
    m = permission
    p = 3
    c = c4+c3+c1+c2+c9+c8
}
one sig rule8 extends Rule{}{
    s =s19
    t =r10
    m = permission
    p = 2
    c = c0+c7
}
one sig rule9 extends Rule{}{
    s =s18
    t =r11
    m = prohibition
    p = 0
    c = c3+c7+c6
}
one sig rule10 extends Rule{}{
    s =s10
    t =r2
    m = permission
    p = 1
    c = c8+c2+c6+c7+c3+c0+c1
}
one sig rule11 extends Rule{}{
    s =s18
    t =r6
    m = permission
    p = 1
    c = c3+c6+c5+c9+c7+c0
}
one sig rule12 extends Rule{}{
    s =s11
    t =r17
    m = permission
    p = 0
    c = c9
}
one sig rule13 extends Rule{}{
    s =s2
    t =r15
    m = prohibition
    p = 1
    c = c9
}
one sig rule14 extends Rule{}{
    s =s4
    t =r1
    m = prohibition
    p = 4
    c = c7+c6+c2+c8
}
one sig rule15 extends Rule{}{
    s =s19
    t =r1
    m = prohibition
    p = 0
    c = c9
}
one sig rule16 extends Rule{}{
    s =s14
    t =r11
    m = prohibition
    p = 0
    c = c6+c5+c3
}
one sig rule17 extends Rule{}{
    s =s6
    t =r19
    m = permission
    p = 1
    c = c2+c5+c7+c4
}
one sig rule18 extends Rule{}{
    s =s8
    t =r12
    m = permission
    p = 0
    c = c3+c7+c4+c1
}
one sig rule19 extends Rule{}{
    s =s15
    t =r11
    m = prohibition
    p = 2
    c = c4+c3+c9+c1+c0+c5
}
one sig rule20 extends Rule{}{
    s =s14
    t =r12
    m = prohibition
    p = 4
    c = c2+c1+c9+c8+c4+c5+c6+c0
}
one sig rule21 extends Rule{}{
    s =s2
    t =r17
    m = permission
    p = 3
    c = c4+c5
}
one sig rule22 extends Rule{}{
    s =s19
    t =r5
    m = prohibition
    p = 1
    c = c3+c5+c4
}
one sig rule23 extends Rule{}{
    s =s0
    t =r0
    m = prohibition
    p = 0
    c = c5+c7+c6+c9
}
one sig rule24 extends Rule{}{
    s =s7
    t =r9
    m = prohibition
    p = 4
    c = c5+c9+c2
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