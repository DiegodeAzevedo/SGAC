module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s4+
         s6->s5+
         s7->s2+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s10+
         s12->s1+
         s12->s6+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s3+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s19->s1+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s13}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r3+
         r5->r3+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r3+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r7+
         r11->r0+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r6+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r12+
         r17->r13+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r9+
         r19->r11+
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
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r0
    m = permission
    p = 2
    c = c9+c0+c7+c2+c5
}
one sig rule1 extends Rule{}{
    s =s0
    t =r1
    m = prohibition
    p = 4
    c = c2+c5+c4+c0
}
one sig rule2 extends Rule{}{
    s =s8
    t =r15
    m = permission
    p = 0
    c = c3+c7+c8
}
one sig rule3 extends Rule{}{
    s =s16
    t =r13
    m = permission
    p = 3
    c = c4+c3+c8+c5+c7
}
one sig rule4 extends Rule{}{
    s =s12
    t =r18
    m = permission
    p = 0
    c = c8+c9+c2+c0
}
one sig rule5 extends Rule{}{
    s =s12
    t =r8
    m = permission
    p = 4
    c = c6+c7+c8+c2+c0
}
one sig rule6 extends Rule{}{
    s =s14
    t =r5
    m = permission
    p = 1
    c = c5+c0+c4+c7+c6+c2
}
one sig rule7 extends Rule{}{
    s =s11
    t =r9
    m = permission
    p = 2
    c = c0+c8+c7
}
one sig rule8 extends Rule{}{
    s =s15
    t =r18
    m = permission
    p = 3
    c = c5+c3+c7+c0+c1+c4+c2
}
one sig rule9 extends Rule{}{
    s =s11
    t =r7
    m = prohibition
    p = 2
    c = c6+c9
}
one sig rule10 extends Rule{}{
    s =s16
    t =r16
    m = prohibition
    p = 4
    c = c0+c9+c4+c6+c3+c8+c1
}
one sig rule11 extends Rule{}{
    s =s7
    t =r9
    m = permission
    p = 1
    c = c2+c6+c9+c0+c8+c1
}
one sig rule12 extends Rule{}{
    s =s13
    t =r1
    m = permission
    p = 1
    c = c6+c7+c5+c4
}
one sig rule13 extends Rule{}{
    s =s2
    t =r11
    m = prohibition
    p = 3
    c = c7+c5+c9+c0
}
one sig rule14 extends Rule{}{
    s =s7
    t =r8
    m = permission
    p = 3
    c = c4+c7+c2+c0+c8+c5
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