module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s8->s2+
         s8->s3+
         s8->s5+
         s9->s0+
         s9->s2+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s5+
         s11->s0+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s7+
         s15->s9+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s13+
         s16->s15+
         s17->s2+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s12+
         s18->s13+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r4+
         r9->r4+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r5+
         r11->r7+
         r12->r3+
         r12->r5+
         r12->r6+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r5+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r0
    m = permission
    p = 4
    c = c8+c4+c1+c9
}
one sig rule1 extends Rule{}{
    s =s11
    t =r8
    m = prohibition
    p = 2
    c = c5+c3
}
one sig rule2 extends Rule{}{
    s =s11
    t =r17
    m = prohibition
    p = 3
    c = c0+c3+c1+c8+c4+c5
}
one sig rule3 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 2
    c = c1+c4
}
one sig rule4 extends Rule{}{
    s =s17
    t =r6
    m = permission
    p = 3
    c = c9
}
one sig rule5 extends Rule{}{
    s =s8
    t =r18
    m = permission
    p = 3
    c = c3+c2+c8+c6+c1+c7+c5
}
one sig rule6 extends Rule{}{
    s =s0
    t =r18
    m = permission
    p = 3
    c = c7+c2+c9
}
one sig rule7 extends Rule{}{
    s =s16
    t =r0
    m = prohibition
    p = 4
    c = c0+c4+c6+c8+c9
}
one sig rule8 extends Rule{}{
    s =s17
    t =r6
    m = permission
    p = 3
    c = c5+c9+c3
}
one sig rule9 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 3
    c = c5+c8+c9+c1+c2
}
one sig rule10 extends Rule{}{
    s =s16
    t =r14
    m = prohibition
    p = 0
    c = c8+c1+c4+c7
}
one sig rule11 extends Rule{}{
    s =s11
    t =r12
    m = permission
    p = 3
    c = c8+c7+c2+c5+c1
}
one sig rule12 extends Rule{}{
    s =s8
    t =r4
    m = permission
    p = 3
    c = c7+c3+c6+c4+c1
}
one sig rule13 extends Rule{}{
    s =s17
    t =r2
    m = permission
    p = 1
    c = c1+c8+c6
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
run grantingContextDetermination{grantingContextDet[req4]} for 4 but 1 GrantingContext