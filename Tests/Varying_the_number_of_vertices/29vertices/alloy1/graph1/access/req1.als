module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s5->s0+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s0+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s4+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s10+
         s13->s1+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r2+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r8+
         r12->r0+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r11}

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
    s =s2
    t =r0
    m = prohibition
    p = 4
    c = c7+c3+c8
}
one sig rule1 extends Rule{}{
    s =s5
    t =r7
    m = prohibition
    p = 2
    c = c8+c2+c6+c1+c9
}
one sig rule2 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 4
    c = c4+c1
}
one sig rule3 extends Rule{}{
    s =s10
    t =r10
    m = prohibition
    p = 2
    c = c4+c9+c2+c5
}
one sig rule4 extends Rule{}{
    s =s11
    t =r7
    m = permission
    p = 4
    c = c8+c0+c3+c9+c1
}
one sig rule5 extends Rule{}{
    s =s9
    t =r7
    m = permission
    p = 1
    c = c1+c7
}
one sig rule6 extends Rule{}{
    s =s9
    t =r4
    m = permission
    p = 0
    c = c4+c6+c3+c0+c9
}
one sig rule7 extends Rule{}{
    s =s4
    t =r12
    m = permission
    p = 0
    c = c5+c9+c6+c0+c3
}
one sig rule8 extends Rule{}{
    s =s12
    t =r10
    m = permission
    p = 3
    c = c4+c5+c8+c9+c1+c0+c3
}
one sig rule9 extends Rule{}{
    s =s11
    t =r6
    m = permission
    p = 1
    c = c3+c6+c5+c4+c1+c2+c9
}
one sig rule10 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 2
    c = c4+c0+c5+c8
}
one sig rule11 extends Rule{}{
    s =s0
    t =r5
    m = prohibition
    p = 0
    c = c1+c4+c6+c5+c0
}
one sig rule12 extends Rule{}{
    s =s13
    t =r1
    m = prohibition
    p = 3
    c = c2+c6+c1
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
