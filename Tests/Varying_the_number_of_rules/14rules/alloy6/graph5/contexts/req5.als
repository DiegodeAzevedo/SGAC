module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s5+
         s12->s8+
         s13->s0+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s10+
         s18->s13+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r4->r1+
         r4->r3+
         r6->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r7+
         r9->r3+
         r9->r4+
         r9->r6+
         r10->r5+
         r10->r6+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r9+
         r12->r2+
         r12->r5+
         r12->r7+
         r12->r9+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r7+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r10+
         r15->r0+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r13+
         r17->r0+
         r17->r2+
         r17->r7+
         r17->r8+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r7+
         r18->r10+
         r18->r11+
         r19->r0+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
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
one sig req5 extends Request{}{
sub=s1
res=r5
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r7
    m = permission
    p = 3
    c = c9+c7+c1+c2+c8
}
one sig rule1 extends Rule{}{
    s =s10
    t =r10
    m = permission
    p = 3
    c = c3+c4
}
one sig rule2 extends Rule{}{
    s =s18
    t =r6
    m = prohibition
    p = 3
    c = c0+c8
}
one sig rule3 extends Rule{}{
    s =s14
    t =r7
    m = prohibition
    p = 1
    c = c6+c3+c0+c9+c2+c7
}
one sig rule4 extends Rule{}{
    s =s10
    t =r15
    m = permission
    p = 2
    c = c4+c5+c0+c7
}
one sig rule5 extends Rule{}{
    s =s14
    t =r10
    m = prohibition
    p = 4
    c = c9
}
one sig rule6 extends Rule{}{
    s =s12
    t =r13
    m = permission
    p = 4
    c = c9+c3+c6+c0
}
one sig rule7 extends Rule{}{
    s =s10
    t =r2
    m = prohibition
    p = 2
    c = c6+c1+c2
}
one sig rule8 extends Rule{}{
    s =s14
    t =r13
    m = prohibition
    p = 4
    c = c8+c6+c9+c7+c1+c4
}
one sig rule9 extends Rule{}{
    s =s7
    t =r18
    m = prohibition
    p = 1
    c = c8+c6
}
one sig rule10 extends Rule{}{
    s =s8
    t =r17
    m = prohibition
    p = 0
    c = c6
}
one sig rule11 extends Rule{}{
    s =s16
    t =r16
    m = permission
    p = 2
    c = c5+c3+c0+c1+c4+c6
}
one sig rule12 extends Rule{}{
    s =s8
    t =r17
    m = prohibition
    p = 1
    c = c0+c1
}
one sig rule13 extends Rule{}{
    s =s10
    t =r7
    m = prohibition
    p = 4
    c = c5+c7+c8+c9+c3
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