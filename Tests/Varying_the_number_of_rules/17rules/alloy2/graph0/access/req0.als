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
         s3->s2+
         s4->s0+
         s4->s3+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s11+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s16+
         s18->s2+
         s18->s4+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s15+
         s19->s2+
         s19->s7+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r6+
         r9->r1+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r12+
         r16->r14+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r14+
         r19->r17}

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
    s =s0
    t =r17
    m = prohibition
    p = 2
    c = c6+c8+c0
}
one sig rule1 extends Rule{}{
    s =s9
    t =r11
    m = permission
    p = 4
    c = c8+c9+c3+c1
}
one sig rule2 extends Rule{}{
    s =s4
    t =r18
    m = permission
    p = 3
    c = c2+c3+c8+c7+c9+c6+c5
}
one sig rule3 extends Rule{}{
    s =s18
    t =r9
    m = permission
    p = 1
    c = c7+c1+c4+c3
}
one sig rule4 extends Rule{}{
    s =s19
    t =r12
    m = prohibition
    p = 0
    c = c1+c9+c7+c3+c5
}
one sig rule5 extends Rule{}{
    s =s14
    t =r9
    m = permission
    p = 2
    c = c9+c7
}
one sig rule6 extends Rule{}{
    s =s2
    t =r18
    m = prohibition
    p = 1
    c = c0+c4+c2+c1+c9+c3
}
one sig rule7 extends Rule{}{
    s =s19
    t =r11
    m = permission
    p = 4
    c = c6+c3
}
one sig rule8 extends Rule{}{
    s =s0
    t =r5
    m = permission
    p = 0
    c = c3+c6+c1+c9+c0
}
one sig rule9 extends Rule{}{
    s =s16
    t =r10
    m = permission
    p = 4
    c = c2+c3
}
one sig rule10 extends Rule{}{
    s =s2
    t =r18
    m = prohibition
    p = 3
    c = c0+c6+c7+c9
}
one sig rule11 extends Rule{}{
    s =s0
    t =r1
    m = permission
    p = 0
    c = c7+c0
}
one sig rule12 extends Rule{}{
    s =s13
    t =r8
    m = prohibition
    p = 1
    c = c5+c6+c4
}
one sig rule13 extends Rule{}{
    s =s19
    t =r9
    m = permission
    p = 3
    c = c8+c4+c0+c9
}
one sig rule14 extends Rule{}{
    s =s14
    t =r19
    m = prohibition
    p = 4
    c = c3+c6+c8+c9+c4+c2
}
one sig rule15 extends Rule{}{
    s =s7
    t =r5
    m = permission
    p = 4
    c = c3+c5+c6+c4+c0
}
one sig rule16 extends Rule{}{
    s =s13
    t =r1
    m = permission
    p = 4
    c = c0+c1+c9+c4+c8
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
