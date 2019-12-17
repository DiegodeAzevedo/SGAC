module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s5->s0+
         s5->s1+
         s5->s3+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s7+
         s9->s2+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s3+
         s11->s4+
         s12->s0+
         s12->s3+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s11+
         s15->s1+
         s15->s4+
         s15->s6+
         s15->s9+
         s16->s0+
         s16->s2+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s13+
         s17->s0+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s8+
         s18->s12+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r4+
         r6->r5+
         r7->r4+
         r8->r2+
         r8->r6+
         r9->r0+
         r9->r3+
         r9->r6+
         r10->r0+
         r10->r5+
         r10->r7+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r6+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r2+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r11+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s4
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s0
    t =r17
    m = permission
    p = 4
    c = c9+c5+c8+c0+c6+c7
}
one sig rule1 extends Rule{}{
    s =s11
    t =r9
    m = permission
    p = 3
    c = c3+c5+c7+c4
}
one sig rule2 extends Rule{}{
    s =s16
    t =r8
    m = prohibition
    p = 2
    c = c3+c1+c2+c4+c0+c6
}
one sig rule3 extends Rule{}{
    s =s10
    t =r18
    m = prohibition
    p = 2
    c = c8+c1+c5
}
one sig rule4 extends Rule{}{
    s =s12
    t =r1
    m = prohibition
    p = 0
    c = c1+c9+c6+c5+c0
}
one sig rule5 extends Rule{}{
    s =s17
    t =r18
    m = prohibition
    p = 0
    c = c3+c4+c8+c2
}
one sig rule6 extends Rule{}{
    s =s17
    t =r14
    m = prohibition
    p = 4
    c = c6+c9+c8+c5+c1+c3
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