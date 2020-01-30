module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s2+
         s4->s2+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s9+
         s11->s1+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s15->s0+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s6+
         s17->s8+
         s17->s10+
         s17->s13+
         s17->s14+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s15+
         s18->s17+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r1+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r5+
         r9->r3+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r7+
         r12->r0+
         r12->r2+
         r12->r4+
         r12->r6+
         r12->r8+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r14->r2+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r15
    m = permission
    p = 4
    c = c7+c4+c8+c3+c1+c2
}
one sig rule1 extends Rule{}{
    s =s18
    t =r17
    m = permission
    p = 1
    c = c4+c5+c7+c8
}
one sig rule2 extends Rule{}{
    s =s19
    t =r15
    m = prohibition
    p = 4
    c = c8+c7+c3+c9
}
one sig rule3 extends Rule{}{
    s =s16
    t =r3
    m = prohibition
    p = 0
    c = c3+c1+c7
}
one sig rule4 extends Rule{}{
    s =s13
    t =r11
    m = permission
    p = 4
    c = c8+c6
}
one sig rule5 extends Rule{}{
    s =s6
    t =r6
    m = prohibition
    p = 4
    c = c7+c4+c5
}
one sig rule6 extends Rule{}{
    s =s12
    t =r8
    m = permission
    p = 2
    c = c8+c1+c6
}
one sig rule7 extends Rule{}{
    s =s16
    t =r5
    m = permission
    p = 0
    c = c8+c6+c5+c9
}
one sig rule8 extends Rule{}{
    s =s10
    t =r3
    m = prohibition
    p = 0
    c = c2+c3+c5+c0+c9
}
one sig rule9 extends Rule{}{
    s =s13
    t =r14
    m = prohibition
    p = 4
    c = c6+c5+c4+c3+c1
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