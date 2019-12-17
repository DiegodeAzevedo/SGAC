module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s4->s1+
         s5->s1+
         s5->s3+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s0+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s10+
         s14->s3+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s4+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s13+
         s18->s2+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s14+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s14+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r2+
         r4->r0+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r5+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r4+
         r9->r6+
         r9->r8+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r6+
         r13->r9+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r9+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r11+
         r15->r12+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r7+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r8+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r0
    m = prohibition
    p = 1
    c = c1
}
one sig rule1 extends Rule{}{
    s =s11
    t =r19
    m = permission
    p = 2
    c = c6+c1+c7+c9+c8+c5
}
one sig rule2 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 1
    c = c0+c7+c2+c4+c3+c9+c5
}
one sig rule3 extends Rule{}{
    s =s1
    t =r5
    m = permission
    p = 3
    c = c1+c4+c0+c9+c7+c5+c3
}
one sig rule4 extends Rule{}{
    s =s16
    t =r10
    m = permission
    p = 4
    c = c1+c7+c6+c3+c2
}
one sig rule5 extends Rule{}{
    s =s16
    t =r16
    m = prohibition
    p = 0
    c = c2+c7+c6+c0
}
one sig rule6 extends Rule{}{
    s =s17
    t =r1
    m = prohibition
    p = 3
    c = c4+c0+c1
}
one sig rule7 extends Rule{}{
    s =s3
    t =r14
    m = prohibition
    p = 0
    c = c2+c1+c3
}
one sig rule8 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 3
    c = c3+c0+c6+c2+c5+c8
}
one sig rule9 extends Rule{}{
    s =s10
    t =r14
    m = prohibition
    p = 1
    c = c8+c3+c0+c2+c1+c4
}
one sig rule10 extends Rule{}{
    s =s3
    t =r0
    m = permission
    p = 4
    c = c5+c1+c0+c3
}
one sig rule11 extends Rule{}{
    s =s19
    t =r10
    m = prohibition
    p = 1
    c = c8
}
one sig rule12 extends Rule{}{
    s =s16
    t =r13
    m = prohibition
    p = 2
    c = c8+c1+c3+c6+c9+c5
}
one sig rule13 extends Rule{}{
    s =s18
    t =r9
    m = permission
    p = 4
    c = c6+c1+c2+c9
}
one sig rule14 extends Rule{}{
    s =s6
    t =r10
    m = permission
    p = 1
    c = c0+c5
}
one sig rule15 extends Rule{}{
    s =s8
    t =r13
    m = prohibition
    p = 1
    c = c1+c5
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
run accessReq1_c0{access_condition[req1,c0]} for 4
run accessReq1_c1{access_condition[req1,c1]} for 4
run accessReq1_c2{access_condition[req1,c2]} for 4
run accessReq1_c3{access_condition[req1,c3]} for 4
run accessReq1_c4{access_condition[req1,c4]} for 4
run accessReq1_c5{access_condition[req1,c5]} for 4
run accessReq1_c6{access_condition[req1,c6]} for 4
run accessReq1_c7{access_condition[req1,c7]} for 4
run accessReq1_c8{access_condition[req1,c8]} for 4
run accessReq1_c9{access_condition[req1,c9]} for 4
