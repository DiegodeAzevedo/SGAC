module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s10+
         s18->s11+
         s18->s13+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r4->r1+
         r5->r2+
         r5->r3+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r7+
         r11->r2+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r10+
         r14->r11+
         r15->r1+
         r15->r6+
         r15->r9+
         r15->r10+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r14+
         r17->r3+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r6+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s3
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r3
    m = prohibition
    p = 1
    c = c4+c1+c6
}
one sig rule1 extends Rule{}{
    s =s11
    t =r4
    m = prohibition
    p = 0
    c = c0+c9
}
one sig rule2 extends Rule{}{
    s =s15
    t =r3
    m = prohibition
    p = 3
    c = c2+c3+c1+c0+c4
}
one sig rule3 extends Rule{}{
    s =s6
    t =r9
    m = permission
    p = 1
    c = c7+c5
}
one sig rule4 extends Rule{}{
    s =s5
    t =r6
    m = permission
    p = 4
    c = c8+c6+c2+c9+c3
}
one sig rule5 extends Rule{}{
    s =s1
    t =r12
    m = prohibition
    p = 3
    c = c5
}
one sig rule6 extends Rule{}{
    s =s17
    t =r1
    m = permission
    p = 4
    c = c6+c5+c4
}
one sig rule7 extends Rule{}{
    s =s0
    t =r12
    m = prohibition
    p = 0
    c = c2+c5
}
one sig rule8 extends Rule{}{
    s =s19
    t =r5
    m = prohibition
    p = 2
    c = c2+c9+c1+c0+c5+c3+c7
}
one sig rule9 extends Rule{}{
    s =s0
    t =r16
    m = prohibition
    p = 3
    c = c3+c4+c1+c6+c9+c5
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