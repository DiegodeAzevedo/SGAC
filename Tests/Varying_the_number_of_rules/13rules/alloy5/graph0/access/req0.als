module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s1+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s6+
         s9->s1+
         s9->s3+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s3+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s7+
         s14->s10+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s11+
         s16->s0+
         s16->s2+
         s16->s5+
         s16->s10+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s5+
         s17->s9+
         s17->s12+
         s17->s14+
         s18->s1+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s14+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r4->r0+
         r4->r1+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r7->r3+
         r8->r0+
         r8->r1+
         r8->r5+
         r8->r7+
         r9->r1+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r6+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r4+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r11+
         r16->r14+
         r17->r4+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r4+
         r19->r5+
         r19->r10+
         r19->r13+
         r19->r15+
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
    s =s2
    t =r19
    m = permission
    p = 4
    c = c7+c6+c3+c0+c8
}
one sig rule1 extends Rule{}{
    s =s1
    t =r8
    m = prohibition
    p = 1
    c = c3
}
one sig rule2 extends Rule{}{
    s =s5
    t =r3
    m = prohibition
    p = 1
    c = c6+c5+c2+c4+c9+c7
}
one sig rule3 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 0
    c = c3+c4+c5+c2
}
one sig rule4 extends Rule{}{
    s =s0
    t =r15
    m = permission
    p = 0
    c = c8+c3
}
one sig rule5 extends Rule{}{
    s =s5
    t =r1
    m = prohibition
    p = 2
    c = c7+c1+c4+c6+c2+c9+c8
}
one sig rule6 extends Rule{}{
    s =s0
    t =r5
    m = permission
    p = 3
    c = c9+c4+c5+c6+c1+c3+c2+c7
}
one sig rule7 extends Rule{}{
    s =s13
    t =r9
    m = prohibition
    p = 3
    c = c0+c4+c6+c8+c7
}
one sig rule8 extends Rule{}{
    s =s7
    t =r19
    m = prohibition
    p = 1
    c = c5+c9+c3+c2+c1
}
one sig rule9 extends Rule{}{
    s =s3
    t =r6
    m = permission
    p = 3
    c = c7+c8+c6+c5+c4
}
one sig rule10 extends Rule{}{
    s =s10
    t =r5
    m = prohibition
    p = 1
    c = c7+c0+c9+c3
}
one sig rule11 extends Rule{}{
    s =s8
    t =r18
    m = prohibition
    p = 4
    c = c9+c0+c1+c4+c6+c8
}
one sig rule12 extends Rule{}{
    s =s8
    t =r5
    m = permission
    p = 3
    c = c2
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
