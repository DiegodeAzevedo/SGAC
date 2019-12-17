module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s3->s2+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s4+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s8+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s12+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s6+
         s18->s8+
         s18->s15+
         s19->s0+
         s19->s4+
         s19->s5+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r5->r2+
         r6->r1+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r3+
         r12->r6+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r4+
         r16->r6+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r16+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s2
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r7
    m = prohibition
    p = 4
    c = c8+c2+c1+c9+c3
}
one sig rule1 extends Rule{}{
    s =s13
    t =r15
    m = permission
    p = 2
    c = c2+c8+c6+c7+c1+c5+c0
}
one sig rule2 extends Rule{}{
    s =s3
    t =r16
    m = permission
    p = 0
    c = c0+c4+c6+c3+c7
}
one sig rule3 extends Rule{}{
    s =s7
    t =r2
    m = prohibition
    p = 2
    c = c6+c7+c8
}
one sig rule4 extends Rule{}{
    s =s12
    t =r12
    m = prohibition
    p = 1
    c = c0+c4
}
one sig rule5 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 4
    c = c3+c2+c9+c8+c5+c7+c0
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