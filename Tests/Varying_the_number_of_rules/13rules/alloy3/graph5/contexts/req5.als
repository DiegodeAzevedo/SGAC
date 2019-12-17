module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s5->s1+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s5+
         s7->s2+
         s7->s6+
         s8->s2+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s2+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s5+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s15->s1+
         s15->s2+
         s15->s8+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s14+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r1+
         r3->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r7->r0+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r7+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r3+
         r15->r5+
         r15->r9+
         r15->r11+
         r16->r2+
         r16->r7+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r14+
         r17->r16+
         r18->r3+
         r18->r6+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r15}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s2
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s6
    t =r8
    m = permission
    p = 3
    c = c8+c3+c2+c1+c6
}
one sig rule1 extends Rule{}{
    s =s8
    t =r1
    m = permission
    p = 1
    c = c4
}
one sig rule2 extends Rule{}{
    s =s15
    t =r7
    m = permission
    p = 0
    c = c4
}
one sig rule3 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 1
    c = c3+c1+c5+c6+c4+c2+c0
}
one sig rule4 extends Rule{}{
    s =s16
    t =r12
    m = permission
    p = 0
    c = c2+c3
}
one sig rule5 extends Rule{}{
    s =s1
    t =r11
    m = prohibition
    p = 2
    c = c5+c1+c0
}
one sig rule6 extends Rule{}{
    s =s4
    t =r17
    m = permission
    p = 0
    c = c8+c6+c0+c3+c9
}
one sig rule7 extends Rule{}{
    s =s13
    t =r2
    m = permission
    p = 2
    c = c1+c9+c4+c7+c6
}
one sig rule8 extends Rule{}{
    s =s7
    t =r16
    m = permission
    p = 3
    c = c2+c5
}
one sig rule9 extends Rule{}{
    s =s4
    t =r16
    m = permission
    p = 0
    c = c2+c5+c7+c8+c0+c1+c6
}
one sig rule10 extends Rule{}{
    s =s16
    t =r9
    m = permission
    p = 0
    c = c8+c1
}
one sig rule11 extends Rule{}{
    s =s2
    t =r16
    m = permission
    p = 3
    c = c4+c0+c2+c1+c6
}
one sig rule12 extends Rule{}{
    s =s10
    t =r9
    m = prohibition
    p = 0
    c = c5+c2+c9+c1+c8+c4+c0
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
run grantingContextDetermination{grantingContextDet[req5]} for 4 but 1 GrantingContext