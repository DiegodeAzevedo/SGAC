module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s4->s2+
         s5->s3+
         s5->s4+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s3+
         s7->s4+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s5+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s9+
         s14->s11+
         s15->s0+
         s15->s2+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s11+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s10+
         s16->s11+
         s16->s15+
         s17->s1+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s12+
         s18->s13+
         s18->s14+
         s19->s0+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r7+
         r9->r1+
         r9->r5+
         r9->r8+
         r10->r3+
         r10->r5+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r4+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
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
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r13+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r3+
         r17->r4+
         r17->r8+
         r17->r9+
         r17->r14+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r11+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r3+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r10+
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
one sig req7 extends Request{}{
sub=s3
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r14
    m = prohibition
    p = 4
    c = c6+c1+c7+c0+c4+c3
}
one sig rule1 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 3
    c = c0+c9+c4+c7
}
one sig rule2 extends Rule{}{
    s =s2
    t =r7
    m = permission
    p = 1
    c = c6+c4+c1
}
one sig rule3 extends Rule{}{
    s =s2
    t =r7
    m = prohibition
    p = 0
    c = c4+c0+c5+c3+c2+c1+c7
}
one sig rule4 extends Rule{}{
    s =s17
    t =r16
    m = permission
    p = 3
    c = c5+c2+c1+c4+c7+c3
}
one sig rule5 extends Rule{}{
    s =s0
    t =r14
    m = permission
    p = 0
    c = c2+c1+c8+c9+c5+c7
}
one sig rule6 extends Rule{}{
    s =s7
    t =r18
    m = prohibition
    p = 4
    c = c4+c6
}
one sig rule7 extends Rule{}{
    s =s17
    t =r6
    m = permission
    p = 0
    c = c1+c3+c8
}
one sig rule8 extends Rule{}{
    s =s10
    t =r11
    m = prohibition
    p = 3
    c = c5+c8+c7+c6
}
one sig rule9 extends Rule{}{
    s =s8
    t =r4
    m = permission
    p = 4
    c = c5+c9
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