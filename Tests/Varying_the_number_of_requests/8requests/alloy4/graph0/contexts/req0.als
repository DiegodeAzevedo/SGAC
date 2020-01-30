module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s1+
         s4->s1+
         s4->s2+
         s4->s3+
         s6->s2+
         s6->s5+
         s7->s4+
         s8->s1+
         s8->s2+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s7+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s4+
         s16->s7+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s15+
         s19->s0+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r4->r0+
         r4->r3+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r12+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r11+
         r15->r0+
         r15->r3+
         r15->r6+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r11+
         r16->r13+
         r17->r3+
         r17->r4+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r8+
         r18->r11+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r14+
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
    m = prohibition
    p = 4
    c = c8+c3+c0+c1
}
one sig rule1 extends Rule{}{
    s =s11
    t =r10
    m = prohibition
    p = 0
    c = c2+c6
}
one sig rule2 extends Rule{}{
    s =s19
    t =r6
    m = prohibition
    p = 3
    c = c0
}
one sig rule3 extends Rule{}{
    s =s11
    t =r17
    m = prohibition
    p = 4
    c = c6+c0+c1+c5+c3+c4
}
one sig rule4 extends Rule{}{
    s =s16
    t =r5
    m = prohibition
    p = 3
    c = c4+c3
}
one sig rule5 extends Rule{}{
    s =s7
    t =r14
    m = prohibition
    p = 1
    c = c0+c3+c1+c7+c8
}
one sig rule6 extends Rule{}{
    s =s12
    t =r6
    m = permission
    p = 3
    c = c3+c5+c7
}
one sig rule7 extends Rule{}{
    s =s8
    t =r12
    m = permission
    p = 0
    c = c9+c1+c4
}
one sig rule8 extends Rule{}{
    s =s13
    t =r0
    m = permission
    p = 2
    c = c7+c2+c3+c1+c8+c9
}
one sig rule9 extends Rule{}{
    s =s18
    t =r13
    m = prohibition
    p = 0
    c = c5+c4
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