module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s6->s1+
         s6->s2+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s3+
         s10->s8+
         s11->s3+
         s11->s4+
         s11->s7+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s8+
         s12->s11+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s7+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s11+
         s15->s13+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s13+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s12+
         s18->s15+
         s19->s0+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r6->r2+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r8+
         r11->r1+
         r11->r3+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r5+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r12+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r3+
         r19->r12+
         r19->r14+
         r19->r16+
         r19->r17}

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
    s =s15
    t =r18
    m = prohibition
    p = 4
    c = c0+c7+c9+c8+c6
}
one sig rule1 extends Rule{}{
    s =s19
    t =r19
    m = prohibition
    p = 2
    c = c7+c2+c8+c1+c5+c4
}
one sig rule2 extends Rule{}{
    s =s14
    t =r5
    m = prohibition
    p = 2
    c = c6+c3+c2+c8
}
one sig rule3 extends Rule{}{
    s =s1
    t =r12
    m = permission
    p = 2
    c = c9+c1+c7+c0
}
one sig rule4 extends Rule{}{
    s =s9
    t =r11
    m = prohibition
    p = 4
    c = c6+c9+c3+c8
}
one sig rule5 extends Rule{}{
    s =s15
    t =r11
    m = permission
    p = 3
    c = c8+c2+c7
}
one sig rule6 extends Rule{}{
    s =s13
    t =r19
    m = prohibition
    p = 0
    c = c8+c2+c5+c0
}
one sig rule7 extends Rule{}{
    s =s9
    t =r11
    m = permission
    p = 4
    c = c4+c6+c3+c1
}
one sig rule8 extends Rule{}{
    s =s13
    t =r19
    m = permission
    p = 3
    c = c5+c9+c0+c7+c1+c4+c8
}
one sig rule9 extends Rule{}{
    s =s17
    t =r6
    m = prohibition
    p = 3
    c = c6+c7+c9+c4+c3+c2
}
one sig rule10 extends Rule{}{
    s =s9
    t =r1
    m = prohibition
    p = 3
    c = c7+c5+c8+c2
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