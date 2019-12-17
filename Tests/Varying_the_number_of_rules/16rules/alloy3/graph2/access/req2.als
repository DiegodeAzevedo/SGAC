module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s3+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s1+
         s8->s2+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s6+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s7+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s10+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s8+
         s19->s9+
         s19->s14+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r8+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r4+
         r14->r5+
         r14->r8+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r6+
         r15->r8+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r4+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r14+
         r18->r0+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r10+
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
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r3
    m = prohibition
    p = 2
    c = c5+c7+c8+c1+c9+c2+c6+c4
}
one sig rule1 extends Rule{}{
    s =s6
    t =r11
    m = permission
    p = 2
    c = c4+c7+c8+c6+c1+c2
}
one sig rule2 extends Rule{}{
    s =s13
    t =r2
    m = prohibition
    p = 4
    c = c8+c1+c0
}
one sig rule3 extends Rule{}{
    s =s1
    t =r15
    m = permission
    p = 1
    c = c3+c9+c7+c0
}
one sig rule4 extends Rule{}{
    s =s3
    t =r10
    m = permission
    p = 0
    c = c0+c8+c3+c7+c9+c6
}
one sig rule5 extends Rule{}{
    s =s15
    t =r10
    m = prohibition
    p = 0
    c = c8+c2+c0+c9+c4+c3
}
one sig rule6 extends Rule{}{
    s =s2
    t =r13
    m = prohibition
    p = 1
    c = c4+c2+c6+c3+c9+c1
}
one sig rule7 extends Rule{}{
    s =s14
    t =r10
    m = prohibition
    p = 4
    c = c6+c5+c7
}
one sig rule8 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 2
    c = c4+c7+c3+c1+c6+c9+c5
}
one sig rule9 extends Rule{}{
    s =s11
    t =r14
    m = prohibition
    p = 3
    c = c3+c1+c8+c5+c9+c7+c2
}
one sig rule10 extends Rule{}{
    s =s10
    t =r2
    m = permission
    p = 0
    c = c9
}
one sig rule11 extends Rule{}{
    s =s5
    t =r16
    m = prohibition
    p = 2
    c = c0+c5+c6+c1+c9
}
one sig rule12 extends Rule{}{
    s =s11
    t =r2
    m = permission
    p = 1
    c = c9
}
one sig rule13 extends Rule{}{
    s =s5
    t =r19
    m = permission
    p = 2
    c = c4
}
one sig rule14 extends Rule{}{
    s =s14
    t =r4
    m = permission
    p = 4
    c = c9+c3
}
one sig rule15 extends Rule{}{
    s =s9
    t =r3
    m = prohibition
    p = 4
    c = c2+c1+c8
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
