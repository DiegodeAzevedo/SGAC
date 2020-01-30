module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s1+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s4+
         s8->s6+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s4+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s5+
         s12->s7+
         s12->s8+
         s13->s1+
         s13->s6+
         s13->s9+
         s13->s11+
         s13->s12+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s2+
         s16->s6+
         s16->s7+
         s16->s11+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s8+
         s17->s9+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r1+
         r6->r2+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r10+
         r15->r1+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r12+
         r16->r1+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r1+
         r17->r6+
         r17->r10+
         r17->r11+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r12+
         r19->r17+
         r19->r18}

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
    s =s4
    t =r12
    m = prohibition
    p = 1
    c = c3+c6+c2
}
one sig rule1 extends Rule{}{
    s =s7
    t =r5
    m = permission
    p = 1
    c = c6+c1+c8
}
one sig rule2 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 4
    c = c3+c6+c8+c4+c2+c5
}
one sig rule3 extends Rule{}{
    s =s12
    t =r16
    m = prohibition
    p = 3
    c = c6+c0+c2+c3+c8+c7
}
one sig rule4 extends Rule{}{
    s =s19
    t =r3
    m = prohibition
    p = 3
    c = c3+c0+c1+c5
}
one sig rule5 extends Rule{}{
    s =s15
    t =r1
    m = prohibition
    p = 3
    c = c4+c8+c5
}
one sig rule6 extends Rule{}{
    s =s14
    t =r9
    m = prohibition
    p = 0
    c = c4
}
one sig rule7 extends Rule{}{
    s =s13
    t =r6
    m = prohibition
    p = 0
    c = c3+c8+c0+c4
}
one sig rule8 extends Rule{}{
    s =s0
    t =r7
    m = permission
    p = 4
    c = c8+c3+c6+c0+c9
}
one sig rule9 extends Rule{}{
    s =s1
    t =r13
    m = permission
    p = 0
    c = c7+c3+c6+c0+c2
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