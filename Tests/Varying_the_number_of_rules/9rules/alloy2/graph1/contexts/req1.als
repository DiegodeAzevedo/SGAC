module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s1+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s6->s0+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s9->s3+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s11+
         s15->s0+
         s15->s5+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s8+
         s16->s9+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s2+
         s18->s6+
         s18->s13+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r4+
         r8->r2+
         r8->r4+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r8+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r6+
         r15->r9+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r14+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r13
    m = prohibition
    p = 2
    c = c5+c0+c8+c2
}
one sig rule1 extends Rule{}{
    s =s18
    t =r7
    m = prohibition
    p = 2
    c = c2+c7+c5+c8+c9+c3+c4
}
one sig rule2 extends Rule{}{
    s =s16
    t =r16
    m = permission
    p = 4
    c = c2+c8+c1+c5+c0+c4
}
one sig rule3 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 4
    c = c7+c9
}
one sig rule4 extends Rule{}{
    s =s14
    t =r17
    m = permission
    p = 2
    c = c5+c1+c9+c3
}
one sig rule5 extends Rule{}{
    s =s9
    t =r10
    m = permission
    p = 2
    c = c6+c4+c1+c5+c9+c0+c2
}
one sig rule6 extends Rule{}{
    s =s0
    t =r8
    m = permission
    p = 0
    c = c7+c5+c9+c4+c8
}
one sig rule7 extends Rule{}{
    s =s0
    t =r5
    m = permission
    p = 3
    c = c6+c5+c4
}
one sig rule8 extends Rule{}{
    s =s14
    t =r15
    m = permission
    p = 3
    c = c6+c5+c4+c0+c1+c8
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