module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s4->s0+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s8+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s11+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s9+
         s15->s11+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s11+
         s18->s12+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r2+
         r7->r0+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r4+
         r8->r7+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r7+
         r17->r8+
         r17->r16+
         r18->r0+
         r18->r4+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r16
    m = permission
    p = 0
    c = c2+c4+c0
}
one sig rule1 extends Rule{}{
    s =s0
    t =r10
    m = prohibition
    p = 1
    c = c6
}
one sig rule2 extends Rule{}{
    s =s2
    t =r10
    m = permission
    p = 3
    c = c1+c5+c8+c3
}
one sig rule3 extends Rule{}{
    s =s19
    t =r1
    m = permission
    p = 0
    c = c3
}
one sig rule4 extends Rule{}{
    s =s8
    t =r0
    m = prohibition
    p = 1
    c = c6+c4+c1+c2+c5+c8+c7
}
one sig rule5 extends Rule{}{
    s =s7
    t =r14
    m = prohibition
    p = 1
    c = c7+c1+c8+c9+c3+c2
}
one sig rule6 extends Rule{}{
    s =s9
    t =r0
    m = permission
    p = 1
    c = c1
}
one sig rule7 extends Rule{}{
    s =s2
    t =r7
    m = prohibition
    p = 1
    c = c9+c0+c7+c5+c4+c6
}
one sig rule8 extends Rule{}{
    s =s18
    t =r14
    m = prohibition
    p = 1
    c = c5+c4+c0+c8+c9
}
one sig rule9 extends Rule{}{
    s =s14
    t =r15
    m = permission
    p = 0
    c = c0+c6+c7+c3+c9
}
one sig rule10 extends Rule{}{
    s =s4
    t =r19
    m = prohibition
    p = 4
    c = c8+c0+c9
}
one sig rule11 extends Rule{}{
    s =s9
    t =r12
    m = prohibition
    p = 3
    c = c0
}
one sig rule12 extends Rule{}{
    s =s14
    t =r0
    m = permission
    p = 3
    c = c4+c0+c2
}
one sig rule13 extends Rule{}{
    s =s1
    t =r18
    m = prohibition
    p = 3
    c = c4+c8+c7+c2+c6
}
one sig rule14 extends Rule{}{
    s =s0
    t =r9
    m = prohibition
    p = 1
    c = c9+c8+c2
}
one sig rule15 extends Rule{}{
    s =s3
    t =r13
    m = permission
    p = 3
    c = c9+c2+c3
}
one sig rule16 extends Rule{}{
    s =s15
    t =r19
    m = permission
    p = 0
    c = c0+c2+c4+c7+c6+c3+c1
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
run grantingContextDetermination{grantingContextDet[req1]} for 4 but 1 GrantingContext