module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s3+
         s6->s0+
         s6->s2+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s4+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s3+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s5+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r0+
         r7->r0+
         r7->r2+
         r7->r5+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r7+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r7+
         r18->r10+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18}

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
    s =s2
    t =r8
    m = permission
    p = 1
    c = c2+c4
}
one sig rule1 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 0
    c = c1+c8+c9
}
one sig rule2 extends Rule{}{
    s =s10
    t =r5
    m = permission
    p = 2
    c = c2+c5+c7
}
one sig rule3 extends Rule{}{
    s =s0
    t =r16
    m = prohibition
    p = 0
    c = c2+c6+c5+c1+c3+c9+c8
}
one sig rule4 extends Rule{}{
    s =s10
    t =r3
    m = prohibition
    p = 0
    c = c6+c3
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