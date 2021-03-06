module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s4->s1+
         s4->s2+
         s5->s4+
         s6->s2+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s3+
         s12->s4+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s11+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s11+
         s17->s16+
         s18->s0+
         s18->s3+
         s18->s8+
         s18->s9+
         s18->s13+
         s18->s14+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s7+
         s19->s11+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r3+
         r7->r1+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r13+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r0+
         r19->r4+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r15+
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
    s =s13
    t =r11
    m = prohibition
    p = 0
    c = c0+c2+c5+c8
}
one sig rule1 extends Rule{}{
    s =s19
    t =r19
    m = permission
    p = 0
    c = c3+c5
}
one sig rule2 extends Rule{}{
    s =s6
    t =r12
    m = prohibition
    p = 3
    c = c8+c1+c5+c2+c3+c9+c4
}
one sig rule3 extends Rule{}{
    s =s8
    t =r17
    m = permission
    p = 1
    c = c9
}
one sig rule4 extends Rule{}{
    s =s17
    t =r12
    m = prohibition
    p = 1
    c = c0+c7+c9+c5
}
one sig rule5 extends Rule{}{
    s =s0
    t =r3
    m = prohibition
    p = 4
    c = c3+c0+c6+c7+c9
}
one sig rule6 extends Rule{}{
    s =s7
    t =r10
    m = permission
    p = 1
    c = c1+c9+c4+c2+c8
}
one sig rule7 extends Rule{}{
    s =s14
    t =r8
    m = prohibition
    p = 1
    c = c4+c7+c9+c5+c8+c2
}
one sig rule8 extends Rule{}{
    s =s3
    t =r8
    m = prohibition
    p = 1
    c = c6+c7+c4+c2
}
one sig rule9 extends Rule{}{
    s =s13
    t =r0
    m = permission
    p = 1
    c = c2+c8+c9+c5+c3
}
one sig rule10 extends Rule{}{
    s =s8
    t =r2
    m = permission
    p = 1
    c = c6+c8
}
one sig rule11 extends Rule{}{
    s =s9
    t =r0
    m = permission
    p = 1
    c = c1+c8+c4+c6
}
one sig rule12 extends Rule{}{
    s =s0
    t =r2
    m = permission
    p = 0
    c = c9
}
one sig rule13 extends Rule{}{
    s =s15
    t =r15
    m = prohibition
    p = 3
    c = c4+c0
}
one sig rule14 extends Rule{}{
    s =s18
    t =r7
    m = permission
    p = 3
    c = c9
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
