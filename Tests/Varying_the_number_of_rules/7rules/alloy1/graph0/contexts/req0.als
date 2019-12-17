module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s4->s0+
         s4->s2+
         s5->s1+
         s5->s2+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s6+
         s8->s3+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s8+
         s14->s12+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s15+
         s18->s0+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s16+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s7+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r3+
         r6->r5+
         r7->r6+
         r8->r1+
         r8->r5+
         r8->r6+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r7+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r9+
         r15->r10+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r12+
         r16->r15+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
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
    s =s16
    t =r10
    m = prohibition
    p = 4
    c = c4+c5+c6
}
one sig rule1 extends Rule{}{
    s =s19
    t =r4
    m = prohibition
    p = 1
    c = c0+c1+c9+c6+c2
}
one sig rule2 extends Rule{}{
    s =s2
    t =r2
    m = prohibition
    p = 3
    c = c6+c2+c1
}
one sig rule3 extends Rule{}{
    s =s1
    t =r12
    m = permission
    p = 2
    c = c2+c6+c1+c5+c8
}
one sig rule4 extends Rule{}{
    s =s2
    t =r19
    m = permission
    p = 2
    c = c1+c4
}
one sig rule5 extends Rule{}{
    s =s0
    t =r10
    m = permission
    p = 2
    c = c3+c7+c6
}
one sig rule6 extends Rule{}{
    s =s11
    t =r4
    m = prohibition
    p = 0
    c = c7+c6+c5
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