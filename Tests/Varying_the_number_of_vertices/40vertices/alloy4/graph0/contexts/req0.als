module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s1+
         s4->s2+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s7+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s7+
         s13->s9+
         s14->s0+
         s14->s2+
         s14->s6+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s2+
         s18->s6+
         s18->s14+
         s18->s17+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r4+
         r9->r0+
         r9->r3+
         r9->r4+
         r9->r5+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r7+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r12+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r2+
         r19->r6+
         r19->r7+
         r19->r8+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r14
    m = permission
    p = 3
    c = c8+c7+c5
}
one sig rule1 extends Rule{}{
    s =s10
    t =r15
    m = prohibition
    p = 3
    c = c2
}
one sig rule2 extends Rule{}{
    s =s14
    t =r5
    m = permission
    p = 0
    c = c9+c8+c3+c6+c1+c7
}
one sig rule3 extends Rule{}{
    s =s5
    t =r7
    m = permission
    p = 3
    c = c9+c2+c7+c0+c8+c1+c4
}
one sig rule4 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 0
    c = c2+c0+c3+c5+c4
}
one sig rule5 extends Rule{}{
    s =s17
    t =r15
    m = permission
    p = 2
    c = c0+c2+c1
}
one sig rule6 extends Rule{}{
    s =s17
    t =r8
    m = permission
    p = 3
    c = c5+c6+c8+c1+c0
}
one sig rule7 extends Rule{}{
    s =s13
    t =r11
    m = permission
    p = 1
    c = c1+c5+c0+c3+c9+c6
}
one sig rule8 extends Rule{}{
    s =s14
    t =r3
    m = prohibition
    p = 0
    c = c4+c2+c6+c9
}
one sig rule9 extends Rule{}{
    s =s10
    t =r18
    m = permission
    p = 2
    c = c3
}
one sig rule10 extends Rule{}{
    s =s19
    t =r5
    m = permission
    p = 4
    c = c5+c4
}
one sig rule11 extends Rule{}{
    s =s5
    t =r8
    m = prohibition
    p = 4
    c = c6+c8
}
one sig rule12 extends Rule{}{
    s =s16
    t =r14
    m = prohibition
    p = 1
    c = c6+c1
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