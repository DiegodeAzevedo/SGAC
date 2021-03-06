module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s2+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s4+
         s11->s8+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s9+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r4->r2+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r5+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r6+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r9+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r7+
         r15->r9+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r18->r1+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r8+
         r19->r10+
         r19->r13+
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
one sig req3 extends Request{}{
sub=s0
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s6
    t =r0
    m = prohibition
    p = 4
    c = c1+c7+c3+c4+c9+c6
}
one sig rule1 extends Rule{}{
    s =s19
    t =r16
    m = prohibition
    p = 3
    c = c8+c6
}
one sig rule2 extends Rule{}{
    s =s3
    t =r10
    m = prohibition
    p = 1
    c = c8+c2+c5+c4
}
one sig rule3 extends Rule{}{
    s =s4
    t =r9
    m = permission
    p = 2
    c = c3+c6+c2
}
one sig rule4 extends Rule{}{
    s =s19
    t =r9
    m = prohibition
    p = 4
    c = c6+c7+c2+c8+c5+c9
}
one sig rule5 extends Rule{}{
    s =s1
    t =r4
    m = permission
    p = 3
    c = c6+c0+c8+c7+c3+c9
}
one sig rule6 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 0
    c = c1+c2+c4+c7+c3
}
one sig rule7 extends Rule{}{
    s =s6
    t =r11
    m = prohibition
    p = 0
    c = c2+c5+c1+c9
}
one sig rule8 extends Rule{}{
    s =s11
    t =r1
    m = prohibition
    p = 3
    c = c3
}
one sig rule9 extends Rule{}{
    s =s15
    t =r15
    m = prohibition
    p = 2
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
run grantingContextDetermination{grantingContextDet[req3]} for 4 but 1 GrantingContext