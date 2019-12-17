module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s2+
         s5->s1+
         s5->s4+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s6+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s5+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s4+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s8+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s11+
         s15->s1+
         s15->s2+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s12+
         s18->s16+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r5->r0+
         r5->r2+
         r6->r1+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r9+
         r11->r1+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r2+
         r13->r6+
         r13->r9+
         r13->r10+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r12+
         r15->r1+
         r15->r3+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r5+
         r16->r9+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r3+
         r17->r5+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r5+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r4+
         r19->r7+
         r19->r8+
         r19->r13+
         r19->r15+
         r19->r17}

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
    s =s12
    t =r0
    m = prohibition
    p = 3
    c = c6+c9+c5+c0+c3
}
one sig rule1 extends Rule{}{
    s =s15
    t =r19
    m = prohibition
    p = 3
    c = c1+c8+c6+c0+c3+c9
}
one sig rule2 extends Rule{}{
    s =s12
    t =r13
    m = permission
    p = 0
    c = c2+c1+c7+c6+c8+c3
}
one sig rule3 extends Rule{}{
    s =s7
    t =r10
    m = permission
    p = 1
    c = c1+c4
}
one sig rule4 extends Rule{}{
    s =s14
    t =r9
    m = prohibition
    p = 2
    c = c6+c0+c3+c5
}
one sig rule5 extends Rule{}{
    s =s9
    t =r9
    m = prohibition
    p = 4
    c = c2+c6+c7+c8+c3+c9+c0
}
one sig rule6 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 0
    c = c6
}
one sig rule7 extends Rule{}{
    s =s15
    t =r16
    m = permission
    p = 3
    c = c7+c8+c2+c4+c0+c9+c1
}
one sig rule8 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 4
    c = c5+c7+c9+c2+c6+c3
}
one sig rule9 extends Rule{}{
    s =s19
    t =r5
    m = prohibition
    p = 4
    c = c0+c5+c2+c6+c8
}
one sig rule10 extends Rule{}{
    s =s9
    t =r1
    m = prohibition
    p = 2
    c = c1+c7+c4+c2+c0+c9+c6
}
one sig rule11 extends Rule{}{
    s =s4
    t =r17
    m = permission
    p = 2
    c = c2+c5+c4+c8+c3+c9+c6
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