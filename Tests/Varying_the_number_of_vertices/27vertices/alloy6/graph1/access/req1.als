module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s4->s1+
         s4->s3+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s7->s4+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s8+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r10+
         r12->r8+
         r12->r9+
         r12->r10}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r11
    m = permission
    p = 2
    c = c2+c7+c0+c9+c5+c4
}
one sig rule1 extends Rule{}{
    s =s3
    t =r1
    m = permission
    p = 2
    c = c6
}
one sig rule2 extends Rule{}{
    s =s13
    t =r3
    m = permission
    p = 4
    c = c7
}
one sig rule3 extends Rule{}{
    s =s13
    t =r6
    m = permission
    p = 4
    c = c0+c5+c8+c7+c6+c1
}
one sig rule4 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 0
    c = c9+c6+c1+c8
}
one sig rule5 extends Rule{}{
    s =s2
    t =r5
    m = prohibition
    p = 4
    c = c5+c7+c9
}
one sig rule6 extends Rule{}{
    s =s8
    t =r11
    m = prohibition
    p = 0
    c = c4+c5+c3+c8+c7
}
one sig rule7 extends Rule{}{
    s =s4
    t =r10
    m = permission
    p = 1
    c = c8+c5+c9+c3
}
one sig rule8 extends Rule{}{
    s =s13
    t =r3
    m = permission
    p = 4
    c = c5+c8+c2+c3
}
one sig rule9 extends Rule{}{
    s =s7
    t =r1
    m = permission
    p = 4
    c = c4+c1+c5+c6
}
one sig rule10 extends Rule{}{
    s =s3
    t =r11
    m = prohibition
    p = 4
    c = c3+c8+c5+c7+c9+c1
}
one sig rule11 extends Rule{}{
    s =s5
    t =r0
    m = prohibition
    p = 1
    c = c6+c5+c8+c1+c4+c0
}
one sig rule12 extends Rule{}{
    s =s1
    t =r11
    m = permission
    p = 0
    c = c9+c0
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
