module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s1+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s0+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s9+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s12+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s10+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s19->s0+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s13+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r5->r1+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r7+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r9+
         r12->r10+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r14->r3+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r8+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r14+
         r17->r2+
         r17->r3+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s0
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r11
    m = prohibition
    p = 4
    c = c9+c0
}
one sig rule1 extends Rule{}{
    s =s11
    t =r8
    m = prohibition
    p = 2
    c = c5+c1+c7
}
one sig rule2 extends Rule{}{
    s =s5
    t =r0
    m = prohibition
    p = 4
    c = c3+c2+c1+c7+c6+c8
}
one sig rule3 extends Rule{}{
    s =s18
    t =r3
    m = permission
    p = 3
    c = c0+c3+c9+c7
}
one sig rule4 extends Rule{}{
    s =s16
    t =r4
    m = permission
    p = 0
    c = c9+c0+c3+c4
}
one sig rule5 extends Rule{}{
    s =s16
    t =r13
    m = prohibition
    p = 0
    c = c0
}
one sig rule6 extends Rule{}{
    s =s9
    t =r18
    m = prohibition
    p = 4
    c = c0+c8+c9+c3+c7
}
one sig rule7 extends Rule{}{
    s =s14
    t =r6
    m = permission
    p = 2
    c = c4
}
one sig rule8 extends Rule{}{
    s =s13
    t =r0
    m = permission
    p = 3
    c = c9+c5+c0+c7+c2+c4+c8
}
one sig rule9 extends Rule{}{
    s =s8
    t =r2
    m = permission
    p = 0
    c = c8+c2+c1
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
run grantingContextDetermination{grantingContextDet[req3]} for 4 but 1 GrantingContext