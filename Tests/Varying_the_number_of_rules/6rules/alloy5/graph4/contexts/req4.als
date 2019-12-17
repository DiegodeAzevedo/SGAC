module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s2+
         s6->s3+
         s7->s1+
         s7->s4+
         s7->s5+
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
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s7+
         s12->s0+
         s12->s2+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s7+
         s13->s10+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s9+
         s14->s11+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s10+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s4+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s13+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r6+
         r8->r1+
         r8->r4+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r8+
         r10->r0+
         r10->r7+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r4+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r9+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r8+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r8+
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
one sig req4 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r0
    m = permission
    p = 0
    c = c7+c1+c5+c9+c8
}
one sig rule1 extends Rule{}{
    s =s18
    t =r3
    m = prohibition
    p = 4
    c = c3+c5+c9+c0+c2+c6+c1
}
one sig rule2 extends Rule{}{
    s =s19
    t =r15
    m = permission
    p = 4
    c = c6+c5+c1
}
one sig rule3 extends Rule{}{
    s =s9
    t =r0
    m = permission
    p = 4
    c = c0+c2+c3+c9+c1+c4
}
one sig rule4 extends Rule{}{
    s =s5
    t =r14
    m = prohibition
    p = 1
    c = c6+c1+c0+c7
}
one sig rule5 extends Rule{}{
    s =s15
    t =r10
    m = permission
    p = 4
    c = c6+c2+c5
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
run grantingContextDetermination{grantingContextDet[req4]} for 4 but 1 GrantingContext