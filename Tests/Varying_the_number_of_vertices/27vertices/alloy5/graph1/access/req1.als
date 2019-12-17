module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s3+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s3+
         s10->s5+
         s10->s8+
         s11->s1+
         s11->s2+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s6+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s7+
         s13->s9}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r4->r0+
         r4->r1+
         r5->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r5+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r5+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r6
    m = prohibition
    p = 3
    c = c1
}
one sig rule1 extends Rule{}{
    s =s1
    t =r4
    m = permission
    p = 2
    c = c1+c4+c6+c5+c0
}
one sig rule2 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 4
    c = c7+c8+c2+c9+c0+c6
}
one sig rule3 extends Rule{}{
    s =s12
    t =r12
    m = permission
    p = 0
    c = c3
}
one sig rule4 extends Rule{}{
    s =s7
    t =r7
    m = permission
    p = 2
    c = c7+c4+c5+c1+c6+c9+c2+c8
}
one sig rule5 extends Rule{}{
    s =s13
    t =r5
    m = permission
    p = 2
    c = c2+c9+c3+c0+c5+c4
}
one sig rule6 extends Rule{}{
    s =s5
    t =r8
    m = permission
    p = 2
    c = c4+c6+c9+c7+c5+c0
}
one sig rule7 extends Rule{}{
    s =s3
    t =r12
    m = prohibition
    p = 0
    c = c0
}
one sig rule8 extends Rule{}{
    s =s0
    t =r6
    m = prohibition
    p = 1
    c = c1+c6+c4+c5+c3
}
one sig rule9 extends Rule{}{
    s =s5
    t =r7
    m = prohibition
    p = 4
    c = c5+c2+c8+c6+c4
}
one sig rule10 extends Rule{}{
    s =s3
    t =r2
    m = prohibition
    p = 0
    c = c0+c6+c5+c1+c7
}
one sig rule11 extends Rule{}{
    s =s12
    t =r10
    m = permission
    p = 0
    c = c2+c5+c3+c4
}
one sig rule12 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 2
    c = c0+c3+c7+c9+c8
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
