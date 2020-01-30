module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s3+
         s8->s2+
         s8->s3+
         s8->s5+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s8+
         s13->s10+
         s14->s4+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r4+
         r7->r1+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r9+
         r13->r0+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r3+
         r14->r6+
         r14->r7+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r7+
         r17->r10+
         r17->r12+
         r17->r14+
         r18->r2+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r3+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r17+
         r19->r18}

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
    s =s19
    t =r2
    m = prohibition
    p = 3
    c = c7+c4+c2+c5+c1
}
one sig rule1 extends Rule{}{
    s =s3
    t =r11
    m = prohibition
    p = 0
    c = c2+c8
}
one sig rule2 extends Rule{}{
    s =s11
    t =r19
    m = prohibition
    p = 3
    c = c2+c7+c9
}
one sig rule3 extends Rule{}{
    s =s9
    t =r10
    m = permission
    p = 4
    c = c5+c2+c0
}
one sig rule4 extends Rule{}{
    s =s13
    t =r4
    m = permission
    p = 2
    c = c8+c2+c7+c1+c4+c3
}
one sig rule5 extends Rule{}{
    s =s2
    t =r0
    m = prohibition
    p = 2
    c = c7+c1
}
one sig rule6 extends Rule{}{
    s =s2
    t =r7
    m = permission
    p = 3
    c = c0+c4
}
one sig rule7 extends Rule{}{
    s =s5
    t =r3
    m = prohibition
    p = 4
    c = c1+c3+c0+c9+c7+c2
}
one sig rule8 extends Rule{}{
    s =s14
    t =r10
    m = prohibition
    p = 3
    c = c8+c6+c1
}
one sig rule9 extends Rule{}{
    s =s17
    t =r13
    m = prohibition
    p = 2
    c = c3+c9+c0+c4+c1+c7
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
