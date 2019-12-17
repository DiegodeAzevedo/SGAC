module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s1+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s7+
         s11->s8+
         s12->s2+
         s12->s5+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s9+
         s14->s11+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s10+
         s17->s12+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r4->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r7->r1+
         r8->r0+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r5+
         r10->r8+
         r11->r5+
         r11->r6+
         r11->r7+
         r12->r0+
         r12->r3+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r3+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r15+
         r19->r16+
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
    s =s3
    t =r17
    m = prohibition
    p = 3
    c = c9+c4+c8+c3+c0+c1+c6
}
one sig rule1 extends Rule{}{
    s =s9
    t =r16
    m = permission
    p = 0
    c = c0+c1+c2+c3+c4
}
one sig rule2 extends Rule{}{
    s =s13
    t =r14
    m = prohibition
    p = 1
    c = c7+c1+c4+c0+c8+c9
}
one sig rule3 extends Rule{}{
    s =s17
    t =r0
    m = prohibition
    p = 0
    c = c5+c8
}
one sig rule4 extends Rule{}{
    s =s1
    t =r6
    m = permission
    p = 1
    c = c9+c7+c4
}
one sig rule5 extends Rule{}{
    s =s15
    t =r11
    m = prohibition
    p = 2
    c = c5+c4+c2+c1+c6
}
one sig rule6 extends Rule{}{
    s =s16
    t =r19
    m = permission
    p = 4
    c = c4
}
one sig rule7 extends Rule{}{
    s =s1
    t =r3
    m = prohibition
    p = 3
    c = c8+c1+c9+c3+c0+c7
}
one sig rule8 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 0
    c = c9+c4+c6+c5
}
one sig rule9 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 0
    c = c5+c7+c4+c1+c9+c6
}
one sig rule10 extends Rule{}{
    s =s5
    t =r18
    m = prohibition
    p = 0
    c = c9
}
one sig rule11 extends Rule{}{
    s =s13
    t =r11
    m = permission
    p = 1
    c = c4+c0+c1+c6
}
one sig rule12 extends Rule{}{
    s =s7
    t =r13
    m = prohibition
    p = 0
    c = c5+c1+c9+c4+c7+c2+c8
}
one sig rule13 extends Rule{}{
    s =s16
    t =r8
    m = permission
    p = 3
    c = c7+c0
}
one sig rule14 extends Rule{}{
    s =s6
    t =r7
    m = permission
    p = 0
    c = c5+c3+c1+c4+c0+c9+c7
}
one sig rule15 extends Rule{}{
    s =s6
    t =r17
    m = permission
    p = 4
    c = c7+c2+c4+c9+c8+c3+c0
}
one sig rule16 extends Rule{}{
    s =s19
    t =r19
    m = permission
    p = 0
    c = c0+c4+c5+c6+c8+c1+c2
}
one sig rule17 extends Rule{}{
    s =s13
    t =r7
    m = prohibition
    p = 2
    c = c5+c7+c1+c6+c8+c2
}
one sig rule18 extends Rule{}{
    s =s14
    t =r7
    m = prohibition
    p = 4
    c = c9+c2
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
