module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s1+
         s7->s0+
         s7->s2+
         s7->s3+
         s8->s0+
         s8->s5+
         s8->s7+
         s9->s6+
         s10->s2+
         s10->s3+
         s10->s7+
         s11->s0+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s5+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s8+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s3+
         s15->s8+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s9+
         s17->s10+
         s17->s15+
         s18->s0+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s9+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r3+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r5+
         r8->r6+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r6+
         r14->r8+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r10+
         r18->r0+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r12+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r10+
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
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 2
    c = c7+c5+c2+c6+c8
}
one sig rule1 extends Rule{}{
    s =s9
    t =r16
    m = permission
    p = 2
    c = c6+c0+c5+c4+c3+c7
}
one sig rule2 extends Rule{}{
    s =s10
    t =r19
    m = permission
    p = 3
    c = c6+c0+c2+c5+c9
}
one sig rule3 extends Rule{}{
    s =s0
    t =r9
    m = permission
    p = 3
    c = c0
}
one sig rule4 extends Rule{}{
    s =s4
    t =r10
    m = prohibition
    p = 0
    c = c2+c8
}
one sig rule5 extends Rule{}{
    s =s5
    t =r13
    m = prohibition
    p = 3
    c = c6+c2+c4+c5+c7+c9+c3+c8
}
one sig rule6 extends Rule{}{
    s =s12
    t =r8
    m = prohibition
    p = 3
    c = c9+c7+c4+c3+c2+c5
}
one sig rule7 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 0
    c = c9+c1
}
one sig rule8 extends Rule{}{
    s =s18
    t =r18
    m = permission
    p = 2
    c = c8+c3+c0+c6+c9
}
one sig rule9 extends Rule{}{
    s =s10
    t =r10
    m = permission
    p = 4
    c = c8+c7
}
one sig rule10 extends Rule{}{
    s =s7
    t =r17
    m = permission
    p = 4
    c = c0+c4+c7+c5+c1+c2
}
one sig rule11 extends Rule{}{
    s =s16
    t =r6
    m = prohibition
    p = 2
    c = c1+c7+c6
}
one sig rule12 extends Rule{}{
    s =s2
    t =r18
    m = permission
    p = 3
    c = c9+c8+c1
}
one sig rule13 extends Rule{}{
    s =s10
    t =r12
    m = permission
    p = 4
    c = c2+c6+c4+c0+c3+c1
}
one sig rule14 extends Rule{}{
    s =s16
    t =r14
    m = prohibition
    p = 3
    c = c3
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