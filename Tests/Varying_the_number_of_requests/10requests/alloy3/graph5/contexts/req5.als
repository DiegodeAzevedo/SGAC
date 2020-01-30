module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s4+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s7+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s8+
         s12->s10+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s15+
         s17->s6+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s2+
         s18->s3+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s12+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r3+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r3+
         r8->r0+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r7+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r10+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r13+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r17+
         r19->r0+
         r19->r4+
         r19->r5+
         r19->r9+
         r19->r12}

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
    s =s13
    t =r3
    m = prohibition
    p = 3
    c = c2+c4+c5+c3+c0+c6
}
one sig rule1 extends Rule{}{
    s =s18
    t =r9
    m = permission
    p = 3
    c = c8+c1+c6+c0
}
one sig rule2 extends Rule{}{
    s =s15
    t =r7
    m = permission
    p = 4
    c = c4+c2+c0+c5+c1+c9+c3+c8
}
one sig rule3 extends Rule{}{
    s =s9
    t =r7
    m = permission
    p = 2
    c = c9+c6+c8+c7
}
one sig rule4 extends Rule{}{
    s =s3
    t =r6
    m = permission
    p = 1
    c = c4+c2+c8+c9+c0+c1
}
one sig rule5 extends Rule{}{
    s =s15
    t =r16
    m = prohibition
    p = 3
    c = c6+c2+c4+c5+c3
}
one sig rule6 extends Rule{}{
    s =s1
    t =r17
    m = prohibition
    p = 0
    c = c8
}
one sig rule7 extends Rule{}{
    s =s14
    t =r10
    m = prohibition
    p = 2
    c = c5+c3+c6+c9+c4+c8+c7
}
one sig rule8 extends Rule{}{
    s =s5
    t =r17
    m = permission
    p = 3
    c = c4+c2+c8+c7
}
one sig rule9 extends Rule{}{
    s =s1
    t =r17
    m = permission
    p = 2
    c = c4+c7+c0+c1+c9
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