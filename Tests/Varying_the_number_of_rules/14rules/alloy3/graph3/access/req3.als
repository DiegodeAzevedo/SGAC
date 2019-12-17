module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s7+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s7+
         s11->s0+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s11+
         s17->s0+
         s17->s2+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s12+
         s18->s17+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r2+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r6+
         r8->r0+
         r8->r5+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r6+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r1+
         r11->r4+
         r11->r8+
         r11->r10+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r8+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r8+
         r18->r9+
         r18->r12+
         r18->r13+
         r18->r17+
         r19->r3+
         r19->r4+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r13+
         r19->r14+
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
one sig req3 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r3
    m = prohibition
    p = 4
    c = c3
}
one sig rule1 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 2
    c = c0+c4
}
one sig rule2 extends Rule{}{
    s =s12
    t =r8
    m = prohibition
    p = 4
    c = c7
}
one sig rule3 extends Rule{}{
    s =s17
    t =r12
    m = prohibition
    p = 2
    c = c7+c8+c1+c2
}
one sig rule4 extends Rule{}{
    s =s19
    t =r17
    m = prohibition
    p = 4
    c = c4
}
one sig rule5 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 1
    c = c8+c1+c5+c7+c6
}
one sig rule6 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 0
    c = c1+c4+c9+c8+c3+c5+c2+c0
}
one sig rule7 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 3
    c = c2+c6+c4+c3+c1+c7
}
one sig rule8 extends Rule{}{
    s =s18
    t =r16
    m = prohibition
    p = 2
    c = c5+c7+c3+c2
}
one sig rule9 extends Rule{}{
    s =s6
    t =r0
    m = prohibition
    p = 3
    c = c3+c8+c2+c0+c5+c9
}
one sig rule10 extends Rule{}{
    s =s4
    t =r13
    m = permission
    p = 3
    c = c7+c4+c9+c3+c6
}
one sig rule11 extends Rule{}{
    s =s12
    t =r11
    m = permission
    p = 3
    c = c8+c0+c1+c4+c6
}
one sig rule12 extends Rule{}{
    s =s0
    t =r16
    m = permission
    p = 3
    c = c3+c4+c5+c7
}
one sig rule13 extends Rule{}{
    s =s19
    t =r4
    m = permission
    p = 0
    c = c7+c6+c3
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
