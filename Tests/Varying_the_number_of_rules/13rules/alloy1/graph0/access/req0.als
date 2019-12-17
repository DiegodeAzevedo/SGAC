module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s1+
         s6->s0+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s4+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s9+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s9+
         s12->s10+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s7+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s15+
         s18->s1+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s13+
         s18->s15+
         s18->s16+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r4->r1+
         r4->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r9->r1+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r9+
         r14->r11+
         r14->r13+
         r15->r2+
         r15->r5+
         r15->r8+
         r15->r9+
         r15->r12+
         r15->r14+
         r16->r4+
         r16->r7+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r16+
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
    s =s4
    t =r5
    m = permission
    p = 0
    c = c0+c2+c1+c9
}
one sig rule1 extends Rule{}{
    s =s3
    t =r15
    m = permission
    p = 3
    c = c3+c6
}
one sig rule2 extends Rule{}{
    s =s3
    t =r11
    m = prohibition
    p = 1
    c = c1+c4+c8+c6+c7+c9+c2
}
one sig rule3 extends Rule{}{
    s =s3
    t =r19
    m = prohibition
    p = 3
    c = c8+c1
}
one sig rule4 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 4
    c = c4
}
one sig rule5 extends Rule{}{
    s =s8
    t =r19
    m = permission
    p = 0
    c = c9+c5+c7+c8+c4
}
one sig rule6 extends Rule{}{
    s =s12
    t =r10
    m = permission
    p = 3
    c = c6+c8+c7+c4+c1
}
one sig rule7 extends Rule{}{
    s =s4
    t =r18
    m = prohibition
    p = 2
    c = c2+c8+c3+c0+c1+c4+c6
}
one sig rule8 extends Rule{}{
    s =s2
    t =r12
    m = prohibition
    p = 3
    c = c2+c0+c1+c7+c3+c6
}
one sig rule9 extends Rule{}{
    s =s16
    t =r1
    m = prohibition
    p = 3
    c = c9
}
one sig rule10 extends Rule{}{
    s =s10
    t =r17
    m = prohibition
    p = 0
    c = c4+c1
}
one sig rule11 extends Rule{}{
    s =s5
    t =r5
    m = permission
    p = 3
    c = c8+c7+c2+c9
}
one sig rule12 extends Rule{}{
    s =s11
    t =r5
    m = permission
    p = 4
    c = c0
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
