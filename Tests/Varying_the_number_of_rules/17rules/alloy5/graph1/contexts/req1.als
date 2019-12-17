module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s5+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s7+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s8+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s5+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s3+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s8+
         s17->s1+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s8+
         s18->s13+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r2+
         r6->r1+
         r6->r2+
         r7->r0+
         r7->r1+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r14->r5+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r4+
         r19->r5+
         r19->r9+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r5
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r5
    m = permission
    p = 2
    c = c5+c7+c1+c8+c3+c6+c9
}
one sig rule1 extends Rule{}{
    s =s14
    t =r12
    m = permission
    p = 1
    c = c7+c3+c9+c4+c8+c0
}
one sig rule2 extends Rule{}{
    s =s5
    t =r4
    m = permission
    p = 0
    c = c1+c3+c0+c7+c2
}
one sig rule3 extends Rule{}{
    s =s6
    t =r4
    m = permission
    p = 0
    c = c5+c2+c6+c0
}
one sig rule4 extends Rule{}{
    s =s6
    t =r19
    m = prohibition
    p = 1
    c = c7+c2+c3
}
one sig rule5 extends Rule{}{
    s =s7
    t =r7
    m = permission
    p = 3
    c = c3+c5+c2+c8+c4
}
one sig rule6 extends Rule{}{
    s =s9
    t =r15
    m = prohibition
    p = 1
    c = c3+c1+c2+c8+c7+c9
}
one sig rule7 extends Rule{}{
    s =s4
    t =r14
    m = prohibition
    p = 4
    c = c7+c5+c9+c8+c4+c3
}
one sig rule8 extends Rule{}{
    s =s18
    t =r19
    m = prohibition
    p = 4
    c = c3+c8+c7+c5+c2+c1+c0
}
one sig rule9 extends Rule{}{
    s =s2
    t =r19
    m = prohibition
    p = 4
    c = c7
}
one sig rule10 extends Rule{}{
    s =s12
    t =r13
    m = permission
    p = 0
    c = c0
}
one sig rule11 extends Rule{}{
    s =s17
    t =r13
    m = permission
    p = 0
    c = c6+c4+c7+c2+c3
}
one sig rule12 extends Rule{}{
    s =s4
    t =r6
    m = permission
    p = 3
    c = c7+c9+c1+c0+c3
}
one sig rule13 extends Rule{}{
    s =s1
    t =r5
    m = prohibition
    p = 4
    c = c5+c0+c4+c2+c1+c7+c3+c8+c6
}
one sig rule14 extends Rule{}{
    s =s11
    t =r1
    m = prohibition
    p = 1
    c = c7+c3+c5+c9+c1+c8+c0
}
one sig rule15 extends Rule{}{
    s =s14
    t =r10
    m = prohibition
    p = 4
    c = c9+c8+c2+c3+c4+c7+c5
}
one sig rule16 extends Rule{}{
    s =s1
    t =r1
    m = permission
    p = 4
    c = c7
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