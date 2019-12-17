module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s4->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s3+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s2+
         s15->s6+
         s15->s7+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s3+
         s18->s4+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s8+
         s19->s13+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r6+
         r8->r1+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r3+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r6+
         r15->r8+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r8+
         r16->r10+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r1+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
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
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s6
    t =r18
    m = prohibition
    p = 1
    c = c3+c6+c5+c8
}
one sig rule1 extends Rule{}{
    s =s18
    t =r11
    m = prohibition
    p = 3
    c = c7
}
one sig rule2 extends Rule{}{
    s =s18
    t =r14
    m = permission
    p = 0
    c = c7+c0
}
one sig rule3 extends Rule{}{
    s =s12
    t =r3
    m = permission
    p = 3
    c = c8+c6+c0+c3
}
one sig rule4 extends Rule{}{
    s =s5
    t =r19
    m = permission
    p = 0
    c = c2
}
one sig rule5 extends Rule{}{
    s =s10
    t =r8
    m = prohibition
    p = 0
    c = c0+c6
}
one sig rule6 extends Rule{}{
    s =s4
    t =r4
    m = prohibition
    p = 0
    c = c1+c3
}
one sig rule7 extends Rule{}{
    s =s1
    t =r18
    m = prohibition
    p = 4
    c = c2+c8+c6+c1
}
one sig rule8 extends Rule{}{
    s =s18
    t =r8
    m = permission
    p = 0
    c = c3+c9+c1+c8+c2+c6
}
one sig rule9 extends Rule{}{
    s =s3
    t =r10
    m = permission
    p = 1
    c = c6+c9+c4+c5+c3+c1
}
one sig rule10 extends Rule{}{
    s =s4
    t =r1
    m = prohibition
    p = 2
    c = c3+c8+c4+c5+c6+c0+c7
}
one sig rule11 extends Rule{}{
    s =s16
    t =r2
    m = prohibition
    p = 1
    c = c8+c6+c7+c4+c9+c2
}
one sig rule12 extends Rule{}{
    s =s5
    t =r1
    m = permission
    p = 2
    c = c1+c9+c2+c5+c7+c8
}
one sig rule13 extends Rule{}{
    s =s9
    t =r1
    m = prohibition
    p = 3
    c = c0+c7+c3+c5
}
one sig rule14 extends Rule{}{
    s =s13
    t =r7
    m = prohibition
    p = 2
    c = c1+c7+c9+c5+c0+c2+c6
}
one sig rule15 extends Rule{}{
    s =s13
    t =r15
    m = permission
    p = 0
    c = c2
}
one sig rule16 extends Rule{}{
    s =s0
    t =r18
    m = prohibition
    p = 0
    c = c3+c7+c2
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
