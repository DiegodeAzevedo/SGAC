module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s2+
         s5->s1+
         s5->s2+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s4+
         s9->s0+
         s9->s3+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s5+
         s11->s7+
         s11->s8+
         s12->s6+
         s12->s8+
         s12->s10+
         s13->s6+
         s13->s8+
         s13->s11+
         s14->s5+
         s14->s8+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s12+
         s16->s4+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s13+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s15+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s13+
         s19->s14+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r2+
         r4->r3+
         r5->r0+
         r6->r0+
         r6->r1+
         r6->r4+
         r7->r0+
         r7->r2+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r4+
         r9->r6+
         r10->r1+
         r10->r5+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r6+
         r12->r7+
         r12->r10+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r5+
         r15->r8+
         r15->r12+
         r16->r0+
         r16->r2+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s2
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r8
    m = permission
    p = 2
    c = c6+c4+c0+c3+c9
}
one sig rule1 extends Rule{}{
    s =s0
    t =r1
    m = permission
    p = 0
    c = c7+c4+c3+c8+c0+c1+c6+c2
}
one sig rule2 extends Rule{}{
    s =s4
    t =r14
    m = permission
    p = 3
    c = c5+c4+c0+c7+c8
}
one sig rule3 extends Rule{}{
    s =s18
    t =r0
    m = prohibition
    p = 1
    c = c3
}
one sig rule4 extends Rule{}{
    s =s19
    t =r0
    m = prohibition
    p = 4
    c = c6+c3+c2+c7+c9+c5
}
one sig rule5 extends Rule{}{
    s =s17
    t =r9
    m = prohibition
    p = 3
    c = c8+c1
}
one sig rule6 extends Rule{}{
    s =s16
    t =r9
    m = prohibition
    p = 2
    c = c5+c2+c4+c9+c1
}
one sig rule7 extends Rule{}{
    s =s5
    t =r18
    m = permission
    p = 0
    c = c8+c1+c7+c6
}
one sig rule8 extends Rule{}{
    s =s4
    t =r5
    m = permission
    p = 3
    c = c9+c5+c2+c3
}
one sig rule9 extends Rule{}{
    s =s5
    t =r6
    m = prohibition
    p = 3
    c = c7+c0+c6+c4+c5+c2
}
one sig rule10 extends Rule{}{
    s =s0
    t =r1
    m = prohibition
    p = 1
    c = c2+c7+c1+c9
}
one sig rule11 extends Rule{}{
    s =s15
    t =r9
    m = prohibition
    p = 0
    c = c2+c5
}
one sig rule12 extends Rule{}{
    s =s6
    t =r18
    m = prohibition
    p = 3
    c = c8+c0+c6+c1+c7+c2
}
one sig rule13 extends Rule{}{
    s =s8
    t =r6
    m = permission
    p = 4
    c = c3+c0+c1+c7+c9
}
one sig rule14 extends Rule{}{
    s =s18
    t =r19
    m = permission
    p = 2
    c = c6+c4+c1+c2+c7+c5
}
one sig rule15 extends Rule{}{
    s =s10
    t =r1
    m = prohibition
    p = 3
    c = c6+c5+c1+c7
}
one sig rule16 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 3
    c = c1+c2+c4+c8+c3
}
one sig rule17 extends Rule{}{
    s =s17
    t =r5
    m = permission
    p = 4
    c = c9+c0+c2+c4+c3+c1
}
one sig rule18 extends Rule{}{
    s =s16
    t =r12
    m = permission
    p = 0
    c = c4+c9+c7+c6+c8
}
one sig rule19 extends Rule{}{
    s =s14
    t =r3
    m = permission
    p = 2
    c = c6+c4+c5+c7+c0
}
one sig rule20 extends Rule{}{
    s =s15
    t =r1
    m = prohibition
    p = 1
    c = c9+c7+c4+c1
}
one sig rule21 extends Rule{}{
    s =s14
    t =r1
    m = prohibition
    p = 1
    c = c7+c1+c4+c6+c5
}
one sig rule22 extends Rule{}{
    s =s14
    t =r4
    m = prohibition
    p = 1
    c = c2+c4
}
one sig rule23 extends Rule{}{
    s =s9
    t =r8
    m = prohibition
    p = 0
    c = c7
}
one sig rule24 extends Rule{}{
    s =s9
    t =r0
    m = permission
    p = 2
    c = c3+c2+c4+c7+c1
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