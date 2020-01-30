module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s2+
         s6->s0+
         s6->s1+
         s6->s3+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s9->s0+
         s9->s3+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s7+
         s11->s0+
         s11->s6+
         s12->s0+
         s12->s5+
         s12->s8+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s1+
         s15->s2+
         s15->s11+
         s16->s0+
         s16->s1+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r5->r1+
         r5->r2+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r2+
         r10->r5+
         r10->r6+
         r11->r1+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r7+
         r12->r10+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r10+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r6+
         r14->r8+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r13+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16}

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
    s =s12
    t =r19
    m = prohibition
    p = 1
    c = c4+c7
}
one sig rule1 extends Rule{}{
    s =s1
    t =r7
    m = prohibition
    p = 4
    c = c1+c6+c7
}
one sig rule2 extends Rule{}{
    s =s9
    t =r11
    m = prohibition
    p = 4
    c = c4+c8
}
one sig rule3 extends Rule{}{
    s =s15
    t =r16
    m = permission
    p = 4
    c = c9+c8+c4+c7+c3+c0
}
one sig rule4 extends Rule{}{
    s =s18
    t =r11
    m = prohibition
    p = 2
    c = c2+c6+c1+c7
}
one sig rule5 extends Rule{}{
    s =s7
    t =r2
    m = prohibition
    p = 1
    c = c8+c3+c0+c1+c4
}
one sig rule6 extends Rule{}{
    s =s4
    t =r14
    m = prohibition
    p = 0
    c = c9+c1+c2+c3+c0+c5
}
one sig rule7 extends Rule{}{
    s =s6
    t =r11
    m = permission
    p = 0
    c = c1
}
one sig rule8 extends Rule{}{
    s =s18
    t =r17
    m = permission
    p = 4
    c = c6+c2+c5+c4
}
one sig rule9 extends Rule{}{
    s =s13
    t =r10
    m = prohibition
    p = 1
    c = c6+c4+c0+c5
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