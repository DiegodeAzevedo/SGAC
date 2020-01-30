module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s6+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s8+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s17+
         s19->s1+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r3->r2+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r9+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r3+
         r17->r4+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r5+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r8+
         r19->r9+
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
one sig req7 extends Request{}{
sub=s3
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s13
    t =r9
    m = permission
    p = 2
    c = c4+c8+c7+c2
}
one sig rule1 extends Rule{}{
    s =s13
    t =r2
    m = prohibition
    p = 0
    c = c0+c7+c1+c4
}
one sig rule2 extends Rule{}{
    s =s15
    t =r12
    m = permission
    p = 4
    c = c7+c4+c5+c0+c9+c1
}
one sig rule3 extends Rule{}{
    s =s14
    t =r8
    m = prohibition
    p = 4
    c = c7+c8+c1+c3+c6
}
one sig rule4 extends Rule{}{
    s =s19
    t =r18
    m = permission
    p = 1
    c = c4
}
one sig rule5 extends Rule{}{
    s =s19
    t =r7
    m = prohibition
    p = 1
    c = c9+c4+c5+c3+c1
}
one sig rule6 extends Rule{}{
    s =s9
    t =r13
    m = prohibition
    p = 3
    c = c6+c0+c9
}
one sig rule7 extends Rule{}{
    s =s8
    t =r19
    m = prohibition
    p = 4
    c = c9+c2+c7+c8+c4+c5+c3
}
one sig rule8 extends Rule{}{
    s =s0
    t =r3
    m = permission
    p = 2
    c = c6+c7+c9+c1+c5
}
one sig rule9 extends Rule{}{
    s =s17
    t =r14
    m = prohibition
    p = 4
    c = c7+c6+c9
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
run grantingContextDetermination{grantingContextDet[req7]} for 4 but 1 GrantingContext