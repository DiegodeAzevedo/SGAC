module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s0+
         s5->s0+
         s5->s1+
         s6->s1+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s3+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s6+
         s9->s1+
         s9->s3+
         s9->s7+
         s10->s2+
         s10->s4+
         s10->s6+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s7+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s8+
         s14->s9+
         s14->s11+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s13+
         s17->s16+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s12+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r7->r0+
         r7->r3+
         r7->r4+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r6+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r11+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15}

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
    s =s16
    t =r14
    m = prohibition
    p = 3
    c = c5+c4+c2+c6
}
one sig rule1 extends Rule{}{
    s =s12
    t =r14
    m = prohibition
    p = 1
    c = c1+c2+c4+c0+c6
}
one sig rule2 extends Rule{}{
    s =s0
    t =r11
    m = permission
    p = 2
    c = c1+c7
}
one sig rule3 extends Rule{}{
    s =s14
    t =r11
    m = permission
    p = 3
    c = c2
}
one sig rule4 extends Rule{}{
    s =s4
    t =r16
    m = permission
    p = 2
    c = c8+c1
}
one sig rule5 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 1
    c = c1+c4+c3
}
one sig rule6 extends Rule{}{
    s =s16
    t =r10
    m = permission
    p = 0
    c = c0+c6+c4+c8+c2+c9+c3
}
one sig rule7 extends Rule{}{
    s =s6
    t =r2
    m = prohibition
    p = 3
    c = c4
}
one sig rule8 extends Rule{}{
    s =s11
    t =r12
    m = permission
    p = 1
    c = c9+c6+c0+c1+c5+c3+c2+c8+c4
}
one sig rule9 extends Rule{}{
    s =s8
    t =r15
    m = permission
    p = 2
    c = c3+c0+c9+c8
}
one sig rule10 extends Rule{}{
    s =s17
    t =r8
    m = permission
    p = 0
    c = c6+c8+c3+c7+c5+c0+c4
}
one sig rule11 extends Rule{}{
    s =s2
    t =r7
    m = permission
    p = 0
    c = c1+c2+c0+c4+c9+c5
}
one sig rule12 extends Rule{}{
    s =s3
    t =r12
    m = prohibition
    p = 1
    c = c3+c8+c6+c9
}
one sig rule13 extends Rule{}{
    s =s17
    t =r13
    m = prohibition
    p = 4
    c = c0+c1+c7+c4+c8
}
one sig rule14 extends Rule{}{
    s =s16
    t =r18
    m = permission
    p = 3
    c = c7+c6+c5
}
one sig rule15 extends Rule{}{
    s =s0
    t =r10
    m = prohibition
    p = 4
    c = c1+c4+c6+c0+c8+c3+c5
}
one sig rule16 extends Rule{}{
    s =s2
    t =r12
    m = prohibition
    p = 1
    c = c2+c1+c0+c6
}
one sig rule17 extends Rule{}{
    s =s13
    t =r0
    m = permission
    p = 4
    c = c6+c5+c9+c2+c0+c4+c3
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
