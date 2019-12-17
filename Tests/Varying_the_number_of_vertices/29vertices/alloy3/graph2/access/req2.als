module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14 extends Subject{}{}
fact{
subSucc=s3->s0+
         s5->s0+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s7+
         s13->s11+
         s14->s6+
         s14->s8}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r1+
         r3->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12}

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
    s =s14
    t =r5
    m = prohibition
    p = 3
    c = c5+c4+c6+c7+c2
}
one sig rule1 extends Rule{}{
    s =s1
    t =r13
    m = prohibition
    p = 4
    c = c7+c9+c2+c0+c8+c3
}
one sig rule2 extends Rule{}{
    s =s12
    t =r5
    m = prohibition
    p = 4
    c = c2+c1+c7+c9+c0+c8
}
one sig rule3 extends Rule{}{
    s =s13
    t =r9
    m = permission
    p = 3
    c = c3+c5+c8+c1+c6+c9
}
one sig rule4 extends Rule{}{
    s =s0
    t =r5
    m = prohibition
    p = 0
    c = c3+c8+c1+c5
}
one sig rule5 extends Rule{}{
    s =s13
    t =r12
    m = prohibition
    p = 3
    c = c2+c9+c8+c3+c5
}
one sig rule6 extends Rule{}{
    s =s11
    t =r8
    m = permission
    p = 3
    c = c7+c5+c6
}
one sig rule7 extends Rule{}{
    s =s12
    t =r13
    m = prohibition
    p = 0
    c = c4+c0+c1+c5+c6+c7+c8
}
one sig rule8 extends Rule{}{
    s =s12
    t =r7
    m = permission
    p = 3
    c = c0+c1+c2+c5
}
one sig rule9 extends Rule{}{
    s =s3
    t =r10
    m = prohibition
    p = 0
    c = c3+c7+c9+c2
}
one sig rule10 extends Rule{}{
    s =s11
    t =r5
    m = permission
    p = 0
    c = c1+c9+c3+c0+c5+c7
}
one sig rule11 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 2
    c = c3+c1+c2+c5+c6+c4+c0
}
one sig rule12 extends Rule{}{
    s =s8
    t =r8
    m = prohibition
    p = 3
    c = c9+c7+c4+c1+c2+c0+c5
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
