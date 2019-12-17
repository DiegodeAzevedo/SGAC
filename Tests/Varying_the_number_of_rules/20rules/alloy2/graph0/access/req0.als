module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s1+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s6+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s5+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s10+
         s12->s2+
         s12->s10+
         s13->s2+
         s13->s5+
         s13->s7+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s11+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s14+
         s18->s1+
         s18->s2+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s14+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r9->r1+
         r9->r4+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r9+
         r12->r2+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r9+
         r14->r0+
         r14->r4+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r12+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r11+
         r18->r12+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r15}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r0
    m = prohibition
    p = 2
    c = c0+c3+c5+c7+c4
}
one sig rule1 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 2
    c = c4+c3
}
one sig rule2 extends Rule{}{
    s =s1
    t =r18
    m = prohibition
    p = 2
    c = c4
}
one sig rule3 extends Rule{}{
    s =s5
    t =r11
    m = prohibition
    p = 4
    c = c8+c5+c7+c2
}
one sig rule4 extends Rule{}{
    s =s13
    t =r14
    m = permission
    p = 0
    c = c9+c0+c7+c3+c4
}
one sig rule5 extends Rule{}{
    s =s1
    t =r13
    m = permission
    p = 1
    c = c4+c5+c0+c6+c8+c7
}
one sig rule6 extends Rule{}{
    s =s7
    t =r11
    m = prohibition
    p = 2
    c = c3+c8+c0+c1+c2
}
one sig rule7 extends Rule{}{
    s =s0
    t =r5
    m = prohibition
    p = 0
    c = c3
}
one sig rule8 extends Rule{}{
    s =s11
    t =r0
    m = permission
    p = 4
    c = c2+c0+c7+c6+c3+c9+c8+c1
}
one sig rule9 extends Rule{}{
    s =s9
    t =r1
    m = prohibition
    p = 0
    c = c5+c3+c4
}
one sig rule10 extends Rule{}{
    s =s16
    t =r17
    m = permission
    p = 2
    c = c9+c4+c7+c3
}
one sig rule11 extends Rule{}{
    s =s0
    t =r0
    m = prohibition
    p = 4
    c = c8+c5+c9
}
one sig rule12 extends Rule{}{
    s =s14
    t =r15
    m = permission
    p = 0
    c = c3+c8+c4+c6+c9+c7+c0
}
one sig rule13 extends Rule{}{
    s =s17
    t =r10
    m = prohibition
    p = 1
    c = c1+c9+c5+c0+c6+c2
}
one sig rule14 extends Rule{}{
    s =s12
    t =r8
    m = prohibition
    p = 2
    c = c7+c0+c3+c8+c2+c6+c4
}
one sig rule15 extends Rule{}{
    s =s11
    t =r0
    m = prohibition
    p = 4
    c = c6+c7+c8+c9+c5
}
one sig rule16 extends Rule{}{
    s =s15
    t =r1
    m = prohibition
    p = 1
    c = c2+c3+c6+c9+c8
}
one sig rule17 extends Rule{}{
    s =s18
    t =r9
    m = permission
    p = 0
    c = c7+c4
}
one sig rule18 extends Rule{}{
    s =s17
    t =r5
    m = prohibition
    p = 1
    c = c1+c9+c0+c7+c2
}
one sig rule19 extends Rule{}{
    s =s7
    t =r3
    m = prohibition
    p = 2
    c = c7+c9+c0+c2+c5+c3+c8
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
run accessReq0_c0{access_condition[req0,c0]} for 4
run accessReq0_c1{access_condition[req0,c1]} for 4
run accessReq0_c2{access_condition[req0,c2]} for 4
run accessReq0_c3{access_condition[req0,c3]} for 4
run accessReq0_c4{access_condition[req0,c4]} for 4
run accessReq0_c5{access_condition[req0,c5]} for 4
run accessReq0_c6{access_condition[req0,c6]} for 4
run accessReq0_c7{access_condition[req0,c7]} for 4
run accessReq0_c8{access_condition[req0,c8]} for 4
run accessReq0_c9{access_condition[req0,c9]} for 4
