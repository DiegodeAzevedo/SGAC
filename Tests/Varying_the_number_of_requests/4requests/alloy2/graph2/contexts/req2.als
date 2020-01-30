module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s3+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s0+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s10+
         s17->s13+
         s17->s14+
         s18->s0+
         s18->s3+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s17+
         s19->s3+
         s19->s4+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r4+
         r8->r0+
         r8->r2+
         r8->r4+
         r9->r0+
         r9->r4+
         r9->r5+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r8+
         r11->r10+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r2+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r11+
         r17->r13+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r16+
         r19->r2+
         r19->r5+
         r19->r10+
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
one sig req2 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r17
    m = prohibition
    p = 1
    c = c0+c2+c5+c8
}
one sig rule1 extends Rule{}{
    s =s5
    t =r19
    m = prohibition
    p = 4
    c = c7
}
one sig rule2 extends Rule{}{
    s =s6
    t =r4
    m = permission
    p = 0
    c = c6
}
one sig rule3 extends Rule{}{
    s =s17
    t =r15
    m = prohibition
    p = 4
    c = c1+c7+c9+c6+c8+c5+c0
}
one sig rule4 extends Rule{}{
    s =s12
    t =r19
    m = permission
    p = 4
    c = c5+c1
}
one sig rule5 extends Rule{}{
    s =s14
    t =r2
    m = permission
    p = 4
    c = c6+c1+c2+c3+c4+c7
}
one sig rule6 extends Rule{}{
    s =s12
    t =r19
    m = permission
    p = 2
    c = c7+c6+c9+c3+c5
}
one sig rule7 extends Rule{}{
    s =s5
    t =r12
    m = prohibition
    p = 1
    c = c4+c0+c5+c8+c7+c9
}
one sig rule8 extends Rule{}{
    s =s12
    t =r9
    m = prohibition
    p = 4
    c = c2+c5+c9+c4+c8+c3
}
one sig rule9 extends Rule{}{
    s =s14
    t =r2
    m = prohibition
    p = 4
    c = c3+c1+c4+c9+c6+c5
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
run grantingContextDetermination{grantingContextDet[req2]} for 4 but 1 GrantingContext