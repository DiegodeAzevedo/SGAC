module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s3+
         s5->s4+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s3+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s8+
         s12->s9+
         s13->s0+
         s13->s2+
         s13->s4+
         s13->s7+
         s13->s10+
         s13->s11+
         s14->s1+
         s14->s3+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s13+
         s15->s14+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s14+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r4+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r8+
         r15->r13+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r11+
         r16->r12+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r4+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s3
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s19
    t =r13
    m = permission
    p = 4
    c = c1+c7+c5
}
one sig rule1 extends Rule{}{
    s =s6
    t =r9
    m = permission
    p = 2
    c = c2+c8+c6+c0+c7+c5
}
one sig rule2 extends Rule{}{
    s =s1
    t =r9
    m = permission
    p = 0
    c = c4
}
one sig rule3 extends Rule{}{
    s =s4
    t =r1
    m = prohibition
    p = 0
    c = c1+c0+c6+c4+c8
}
one sig rule4 extends Rule{}{
    s =s12
    t =r13
    m = prohibition
    p = 0
    c = c5+c7+c9+c2+c4+c0+c1
}
one sig rule5 extends Rule{}{
    s =s15
    t =r3
    m = prohibition
    p = 1
    c = c6+c3
}
one sig rule6 extends Rule{}{
    s =s12
    t =r7
    m = permission
    p = 4
    c = c1
}
one sig rule7 extends Rule{}{
    s =s15
    t =r16
    m = prohibition
    p = 3
    c = c9+c1+c3+c0+c4+c6+c5
}
one sig rule8 extends Rule{}{
    s =s6
    t =r12
    m = prohibition
    p = 1
    c = c9+c0+c1+c4+c8+c3
}
one sig rule9 extends Rule{}{
    s =s1
    t =r9
    m = permission
    p = 1
    c = c8+c2
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