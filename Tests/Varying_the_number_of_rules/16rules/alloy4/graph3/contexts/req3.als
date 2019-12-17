module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s4+
         s6->s0+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s5+
         s11->s6+
         s11->s10+
         s12->s2+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s9+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s9+
         s14->s11+
         s15->s1+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s3+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s14+
         s17->s0+
         s17->s3+
         s17->s6+
         s17->s9+
         s17->s12+
         s17->s16+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s13+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s6+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r1+
         r5->r2+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r5+
         r8->r7+
         r9->r1+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r9+
         r14->r10+
         r14->r13+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r8+
         r15->r13+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r13+
         r17->r0+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r12+
         r19->r14+
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
sub=s2
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r12
    m = prohibition
    p = 3
    c = c5+c3+c7+c8+c1+c2
}
one sig rule1 extends Rule{}{
    s =s9
    t =r17
    m = prohibition
    p = 2
    c = c3+c7+c9
}
one sig rule2 extends Rule{}{
    s =s3
    t =r10
    m = prohibition
    p = 1
    c = c6+c2+c1+c8+c7
}
one sig rule3 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 3
    c = c0
}
one sig rule4 extends Rule{}{
    s =s2
    t =r7
    m = prohibition
    p = 2
    c = c9+c1+c6+c4+c8+c3
}
one sig rule5 extends Rule{}{
    s =s5
    t =r17
    m = permission
    p = 4
    c = c0+c7+c6
}
one sig rule6 extends Rule{}{
    s =s18
    t =r8
    m = permission
    p = 0
    c = c7+c6+c3+c8+c1+c9
}
one sig rule7 extends Rule{}{
    s =s17
    t =r17
    m = permission
    p = 2
    c = c7+c8
}
one sig rule8 extends Rule{}{
    s =s19
    t =r17
    m = permission
    p = 0
    c = c8+c0+c3
}
one sig rule9 extends Rule{}{
    s =s9
    t =r12
    m = prohibition
    p = 3
    c = c6
}
one sig rule10 extends Rule{}{
    s =s11
    t =r11
    m = permission
    p = 1
    c = c5+c3+c2+c4+c6+c7
}
one sig rule11 extends Rule{}{
    s =s11
    t =r1
    m = prohibition
    p = 4
    c = c6
}
one sig rule12 extends Rule{}{
    s =s7
    t =r17
    m = prohibition
    p = 2
    c = c6+c2+c5+c8+c4
}
one sig rule13 extends Rule{}{
    s =s4
    t =r16
    m = prohibition
    p = 2
    c = c0+c9+c7
}
one sig rule14 extends Rule{}{
    s =s16
    t =r6
    m = permission
    p = 1
    c = c7+c1+c8+c2
}
one sig rule15 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 0
    c = c3+c0+c8+c6+c1+c7
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