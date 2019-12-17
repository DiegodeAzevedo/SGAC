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
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s7+
         s10->s1+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s8+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s12+
         s18->s1+
         s18->s5+
         s18->s10+
         s18->s13+
         s18->s15+
         s18->s16+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r3+
         r11->r4+
         r11->r6+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r7+
         r13->r10+
         r14->r3+
         r14->r8+
         r14->r12+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r4+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r13+
         r18->r14+
         r18->r16+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r11
    m = prohibition
    p = 1
    c = c5+c0
}
one sig rule1 extends Rule{}{
    s =s5
    t =r2
    m = permission
    p = 1
    c = c9+c1+c2+c6+c3+c5
}
one sig rule2 extends Rule{}{
    s =s14
    t =r9
    m = prohibition
    p = 1
    c = c8
}
one sig rule3 extends Rule{}{
    s =s13
    t =r11
    m = prohibition
    p = 4
    c = c7+c0+c2+c6+c9+c1+c5
}
one sig rule4 extends Rule{}{
    s =s19
    t =r7
    m = prohibition
    p = 2
    c = c6+c5+c0+c9+c2
}
one sig rule5 extends Rule{}{
    s =s10
    t =r2
    m = prohibition
    p = 4
    c = c8+c1+c4+c3
}
one sig rule6 extends Rule{}{
    s =s4
    t =r19
    m = prohibition
    p = 3
    c = c0+c6+c8
}
one sig rule7 extends Rule{}{
    s =s19
    t =r6
    m = permission
    p = 3
    c = c8+c2+c9+c3+c6+c4
}
one sig rule8 extends Rule{}{
    s =s14
    t =r18
    m = prohibition
    p = 1
    c = c7+c5+c3+c0+c9
}
one sig rule9 extends Rule{}{
    s =s17
    t =r17
    m = permission
    p = 0
    c = c4+c7+c8+c0
}
one sig rule10 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 0
    c = c5+c7+c1+c4
}
one sig rule11 extends Rule{}{
    s =s18
    t =r16
    m = permission
    p = 1
    c = c8+c9+c3+c4+c2
}
one sig rule12 extends Rule{}{
    s =s14
    t =r14
    m = permission
    p = 0
    c = c6+c9+c2+c8+c4+c7+c3
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