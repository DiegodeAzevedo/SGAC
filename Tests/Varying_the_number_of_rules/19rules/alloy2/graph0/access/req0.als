module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s3+
         s5->s1+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s3+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s4+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s2+
         s13->s5+
         s13->s7+
         s13->s9+
         s14->s0+
         s14->s2+
         s14->s5+
         s14->s13+
         s15->s1+
         s15->s4+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s18->s1+
         s18->s4+
         s18->s7+
         s18->s8+
         s18->s9+
         s19->s1+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r2+
         r4->r0+
         r5->r0+
         r5->r2+
         r6->r3+
         r7->r0+
         r7->r3+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r5+
         r10->r7+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r6+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r17+
         r19->r18}

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
    s =s6
    t =r17
    m = prohibition
    p = 0
    c = c0
}
one sig rule1 extends Rule{}{
    s =s0
    t =r0
    m = permission
    p = 2
    c = c2+c9+c8
}
one sig rule2 extends Rule{}{
    s =s6
    t =r6
    m = permission
    p = 4
    c = c6+c3
}
one sig rule3 extends Rule{}{
    s =s9
    t =r19
    m = permission
    p = 2
    c = c3+c6+c0+c7+c5
}
one sig rule4 extends Rule{}{
    s =s6
    t =r2
    m = permission
    p = 4
    c = c3+c5+c1+c2+c9+c0
}
one sig rule5 extends Rule{}{
    s =s1
    t =r10
    m = permission
    p = 0
    c = c8+c6+c3+c7+c9+c0+c1
}
one sig rule6 extends Rule{}{
    s =s13
    t =r9
    m = prohibition
    p = 2
    c = c1+c3+c2+c9+c5
}
one sig rule7 extends Rule{}{
    s =s1
    t =r14
    m = prohibition
    p = 4
    c = c9+c0+c8+c4
}
one sig rule8 extends Rule{}{
    s =s6
    t =r9
    m = permission
    p = 0
    c = c3+c6+c1
}
one sig rule9 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 0
    c = c9+c2+c7+c1+c5+c6
}
one sig rule10 extends Rule{}{
    s =s16
    t =r12
    m = permission
    p = 1
    c = c8+c9+c1+c2+c6+c7+c5
}
one sig rule11 extends Rule{}{
    s =s17
    t =r19
    m = permission
    p = 3
    c = c9+c0
}
one sig rule12 extends Rule{}{
    s =s13
    t =r9
    m = prohibition
    p = 0
    c = c5
}
one sig rule13 extends Rule{}{
    s =s3
    t =r8
    m = permission
    p = 1
    c = c9+c4+c5+c3+c8+c0+c6
}
one sig rule14 extends Rule{}{
    s =s8
    t =r2
    m = permission
    p = 0
    c = c4+c6+c5+c2+c8+c7
}
one sig rule15 extends Rule{}{
    s =s15
    t =r0
    m = prohibition
    p = 1
    c = c5+c4+c1+c8+c3
}
one sig rule16 extends Rule{}{
    s =s11
    t =r9
    m = prohibition
    p = 3
    c = c7+c4
}
one sig rule17 extends Rule{}{
    s =s3
    t =r11
    m = prohibition
    p = 2
    c = c5+c2
}
one sig rule18 extends Rule{}{
    s =s9
    t =r18
    m = prohibition
    p = 4
    c = c2+c6+c0
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
