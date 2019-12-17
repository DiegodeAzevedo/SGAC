module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s6->s0+
         s6->s1+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s9+
         s13->s12+
         s14->s2+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s11+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s10+
         s16->s13+
         s16->s14+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s18->s2+
         s18->s8+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s16+
         s19->s2+
         s19->s3+
         s19->s7+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r2+
         r6->r4+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r6+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r13->r3+
         r13->r6+
         r13->r7+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r10+
         r14->r11+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r12+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r10+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r8
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r15
    m = prohibition
    p = 1
    c = c3+c2
}
one sig rule1 extends Rule{}{
    s =s2
    t =r8
    m = prohibition
    p = 4
    c = c1+c9
}
one sig rule2 extends Rule{}{
    s =s7
    t =r4
    m = prohibition
    p = 0
    c = c0+c6
}
one sig rule3 extends Rule{}{
    s =s9
    t =r3
    m = prohibition
    p = 0
    c = c1+c7+c6+c0+c4
}
one sig rule4 extends Rule{}{
    s =s17
    t =r5
    m = permission
    p = 4
    c = c6+c9+c7+c3+c4+c0+c8
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