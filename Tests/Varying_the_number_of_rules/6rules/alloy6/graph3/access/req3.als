module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s4->s1+
         s4->s2+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s2+
         s7->s1+
         s7->s3+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s13->s6+
         s13->s7+
         s13->s8+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s9+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
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
         s18->s7+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r9+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r6+
         r14->r10+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r11+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r12+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r13+
         r19->r14}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s11
    t =r10
    m = prohibition
    p = 1
    c = c6
}
one sig rule1 extends Rule{}{
    s =s5
    t =r11
    m = prohibition
    p = 3
    c = c8+c5+c1+c0
}
one sig rule2 extends Rule{}{
    s =s0
    t =r10
    m = prohibition
    p = 2
    c = c2
}
one sig rule3 extends Rule{}{
    s =s18
    t =r19
    m = prohibition
    p = 1
    c = c7
}
one sig rule4 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 4
    c = c5+c9
}
one sig rule5 extends Rule{}{
    s =s5
    t =r1
    m = permission
    p = 4
    c = c6+c0+c2+c1+c3+c9
}
//**************************
//***Auxiliary Predicates***
//**************************
pred access_condition[req:Request,con:Context]{
    (no  r:applicableRules[req] |  (evalRuleCond[r,con] and r.m=prohibition and
        all rule: r.^(req.ruleSucc) | not evalRuleCond[rule,con])	)
    and some { r:applicableRules[req] |evalRuleCond[r,con]}
}

//*********************
//***Access property***
//*********************
run accessReq3_c0{access_condition[req3,c0]} for 4
run accessReq3_c1{access_condition[req3,c1]} for 4
run accessReq3_c2{access_condition[req3,c2]} for 4
run accessReq3_c3{access_condition[req3,c3]} for 4
run accessReq3_c4{access_condition[req3,c4]} for 4
run accessReq3_c5{access_condition[req3,c5]} for 4
run accessReq3_c6{access_condition[req3,c6]} for 4
run accessReq3_c7{access_condition[req3,c7]} for 4
run accessReq3_c8{access_condition[req3,c8]} for 4
run accessReq3_c9{access_condition[req3,c9]} for 4
