module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s1+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s4+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s8+
         s13->s1+
         s13->s2+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s4+
         s16->s6+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s8+
         s18->s10+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s8+
         s19->s11+
         s19->s12+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r4+
         r9->r5+
         r10->r0+
         r10->r3+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r10+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r9+
         r15->r12+
         r15->r13+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r11+
         r19->r13+
         r19->r14}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r4
    m = prohibition
    p = 2
    c = c9
}
one sig rule1 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 4
    c = c3+c5+c4+c6+c2+c1
}
one sig rule2 extends Rule{}{
    s =s10
    t =r12
    m = permission
    p = 3
    c = c8+c1+c2+c3+c5
}
one sig rule3 extends Rule{}{
    s =s14
    t =r11
    m = prohibition
    p = 1
    c = c9+c3
}
one sig rule4 extends Rule{}{
    s =s2
    t =r18
    m = prohibition
    p = 4
    c = c8+c1+c3+c4+c7+c5+c6
}
one sig rule5 extends Rule{}{
    s =s15
    t =r5
    m = permission
    p = 1
    c = c9+c1+c4
}
one sig rule6 extends Rule{}{
    s =s18
    t =r11
    m = prohibition
    p = 1
    c = c9+c0
}
one sig rule7 extends Rule{}{
    s =s1
    t =r4
    m = permission
    p = 4
    c = c9+c7+c2+c5+c6+c1+c3
}
one sig rule8 extends Rule{}{
    s =s15
    t =r11
    m = prohibition
    p = 1
    c = c4+c7+c6+c2+c5
}
one sig rule9 extends Rule{}{
    s =s5
    t =r1
    m = prohibition
    p = 4
    c = c9+c3+c6
}
one sig rule10 extends Rule{}{
    s =s19
    t =r4
    m = prohibition
    p = 0
    c = c5+c3
}
one sig rule11 extends Rule{}{
    s =s8
    t =r17
    m = prohibition
    p = 3
    c = c4+c6+c7+c2+c0+c9
}
one sig rule12 extends Rule{}{
    s =s19
    t =r15
    m = permission
    p = 2
    c = c6+c2+c8+c3+c7
}
one sig rule13 extends Rule{}{
    s =s10
    t =r9
    m = prohibition
    p = 2
    c = c7+c4
}
one sig rule14 extends Rule{}{
    s =s14
    t =r7
    m = prohibition
    p = 3
    c = c5+c2+c9+c3+c4+c6
}
one sig rule15 extends Rule{}{
    s =s0
    t =r16
    m = permission
    p = 3
    c = c9
}
one sig rule16 extends Rule{}{
    s =s6
    t =r11
    m = prohibition
    p = 3
    c = c0+c2+c3+c7+c1
}
one sig rule17 extends Rule{}{
    s =s14
    t =r14
    m = prohibition
    p = 4
    c = c9+c2+c7+c6+c1+c3
}
one sig rule18 extends Rule{}{
    s =s1
    t =r6
    m = prohibition
    p = 1
    c = c1+c9+c3+c2+c8
}
one sig rule19 extends Rule{}{
    s =s10
    t =r15
    m = permission
    p = 4
    c = c3+c8
}
one sig rule20 extends Rule{}{
    s =s11
    t =r14
    m = prohibition
    p = 0
    c = c9+c3+c0+c4+c2+c1+c5
}
one sig rule21 extends Rule{}{
    s =s14
    t =r1
    m = permission
    p = 4
    c = c6+c9+c3+c5+c2+c8
}
one sig rule22 extends Rule{}{
    s =s5
    t =r15
    m = permission
    p = 0
    c = c2+c4+c8
}
one sig rule23 extends Rule{}{
    s =s2
    t =r16
    m = permission
    p = 1
    c = c8+c4+c3+c2+c7+c9
}
one sig rule24 extends Rule{}{
    s =s11
    t =r8
    m = prohibition
    p = 4
    c = c9
}
one sig rule25 extends Rule{}{
    s =s0
    t =r16
    m = prohibition
    p = 1
    c = c0+c2+c9
}
one sig rule26 extends Rule{}{
    s =s14
    t =r8
    m = prohibition
    p = 2
    c = c0+c3+c9+c7+c4+c5
}
one sig rule27 extends Rule{}{
    s =s5
    t =r3
    m = permission
    p = 1
    c = c2
}
one sig rule28 extends Rule{}{
    s =s15
    t =r17
    m = permission
    p = 3
    c = c7+c5+c9+c0+c4+c6
}
one sig rule29 extends Rule{}{
    s =s12
    t =r5
    m = permission
    p = 3
    c = c7+c5+c6+c1+c4+c0+c2+c8
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
run accessReq2_c0{access_condition[req2,c0]} for 4
run accessReq2_c1{access_condition[req2,c1]} for 4
run accessReq2_c2{access_condition[req2,c2]} for 4
run accessReq2_c3{access_condition[req2,c3]} for 4
run accessReq2_c4{access_condition[req2,c4]} for 4
run accessReq2_c5{access_condition[req2,c5]} for 4
run accessReq2_c6{access_condition[req2,c6]} for 4
run accessReq2_c7{access_condition[req2,c7]} for 4
run accessReq2_c8{access_condition[req2,c8]} for 4
run accessReq2_c9{access_condition[req2,c9]} for 4
