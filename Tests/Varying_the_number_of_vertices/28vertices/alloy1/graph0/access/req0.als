module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s6+
         s9->s4+
         s9->s6+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s11+
         s13->s12}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r7+
         r9->r3+
         r9->r4+
         r9->r6+
         r10->r2+
         r10->r5+
         r10->r6+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r7+
         r11->r8+
         r12->r0+
         r12->r2+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r8+
         r13->r9}

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
    t =r8
    m = prohibition
    p = 1
    c = c0+c1+c8+c7
}
one sig rule1 extends Rule{}{
    s =s8
    t =r0
    m = permission
    p = 1
    c = c4+c1+c9+c7+c3
}
one sig rule2 extends Rule{}{
    s =s13
    t =r7
    m = permission
    p = 2
    c = c4+c2+c9+c8
}
one sig rule3 extends Rule{}{
    s =s11
    t =r13
    m = permission
    p = 3
    c = c3+c5+c0+c6+c1+c9+c7
}
one sig rule4 extends Rule{}{
    s =s2
    t =r2
    m = prohibition
    p = 2
    c = c0+c2+c9
}
one sig rule5 extends Rule{}{
    s =s4
    t =r11
    m = permission
    p = 3
    c = c7+c5
}
one sig rule6 extends Rule{}{
    s =s3
    t =r4
    m = permission
    p = 0
    c = c5+c0+c1+c8
}
one sig rule7 extends Rule{}{
    s =s12
    t =r6
    m = permission
    p = 0
    c = c7+c5+c8+c1+c9+c0
}
one sig rule8 extends Rule{}{
    s =s2
    t =r6
    m = permission
    p = 0
    c = c1+c4
}
one sig rule9 extends Rule{}{
    s =s11
    t =r5
    m = permission
    p = 3
    c = c1
}
one sig rule10 extends Rule{}{
    s =s11
    t =r1
    m = prohibition
    p = 1
    c = c0+c6+c1+c4+c8
}
one sig rule11 extends Rule{}{
    s =s6
    t =r13
    m = prohibition
    p = 2
    c = c3+c9+c6+c7+c5
}
one sig rule12 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 3
    c = c1+c2+c5+c3
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
