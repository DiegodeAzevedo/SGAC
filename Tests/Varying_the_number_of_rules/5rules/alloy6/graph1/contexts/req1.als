module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s3+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s7+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s5+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s5+
         s14->s7+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s8+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s2+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s15+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r6->r0+
         r6->r2+
         r7->r1+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r3+
         r10->r4+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r9+
         r12->r11+
         r13->r4+
         r13->r6+
         r13->r9+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r4+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r11+
         r15->r12+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r3+
         r19->r10+
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
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r2
    m = permission
    p = 3
    c = c5+c6+c0+c1+c8+c2
}
one sig rule1 extends Rule{}{
    s =s11
    t =r11
    m = permission
    p = 3
    c = c0+c2+c3+c4+c1+c9+c8
}
one sig rule2 extends Rule{}{
    s =s1
    t =r15
    m = permission
    p = 0
    c = c4
}
one sig rule3 extends Rule{}{
    s =s1
    t =r17
    m = permission
    p = 4
    c = c6+c1+c4+c0+c7+c3
}
one sig rule4 extends Rule{}{
    s =s4
    t =r10
    m = prohibition
    p = 0
    c = c4
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