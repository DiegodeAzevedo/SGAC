module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s4+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s5+
         s12->s6+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s7+
         s16->s10+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r5+
         r9->r2+
         r9->r3+
         r9->r6+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r8+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r2+
         r14->r7+
         r14->r10+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r17}

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
    s =s3
    t =r4
    m = prohibition
    p = 0
    c = c2+c5+c3+c6+c9+c7+c0
}
one sig rule1 extends Rule{}{
    s =s5
    t =r12
    m = prohibition
    p = 2
    c = c1+c6+c9+c4+c5+c0
}
one sig rule2 extends Rule{}{
    s =s4
    t =r8
    m = permission
    p = 2
    c = c0+c8+c5+c4
}
one sig rule3 extends Rule{}{
    s =s16
    t =r7
    m = prohibition
    p = 1
    c = c4+c9+c0+c6+c1+c8
}
one sig rule4 extends Rule{}{
    s =s12
    t =r10
    m = permission
    p = 2
    c = c1+c5+c9+c3+c0
}
one sig rule5 extends Rule{}{
    s =s6
    t =r17
    m = prohibition
    p = 3
    c = c5+c8
}
one sig rule6 extends Rule{}{
    s =s19
    t =r11
    m = prohibition
    p = 0
    c = c6+c9+c2+c8
}
one sig rule7 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 0
    c = c0
}
one sig rule8 extends Rule{}{
    s =s18
    t =r18
    m = permission
    p = 0
    c = c3+c2+c9+c5+c4+c1
}
one sig rule9 extends Rule{}{
    s =s19
    t =r7
    m = permission
    p = 3
    c = c8
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