module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s1+
         s4->s2+
         s5->s1+
         s5->s3+
         s6->s1+
         s6->s3+
         s7->s1+
         s7->s2+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s7+
         s10->s1+
         s10->s2+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s6+
         s12->s7+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r1+
         r6->r2+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r7+
         r10->r0+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r12}

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
    s =s8
    t =r2
    m = prohibition
    p = 4
    c = c0+c2
}
one sig rule1 extends Rule{}{
    s =s0
    t =r5
    m = prohibition
    p = 1
    c = c8+c1+c7+c4+c5+c2
}
one sig rule2 extends Rule{}{
    s =s12
    t =r13
    m = permission
    p = 4
    c = c7+c0+c5+c4
}
one sig rule3 extends Rule{}{
    s =s8
    t =r0
    m = prohibition
    p = 3
    c = c2+c4+c6
}
one sig rule4 extends Rule{}{
    s =s3
    t =r0
    m = permission
    p = 4
    c = c0+c7+c3+c2+c1
}
one sig rule5 extends Rule{}{
    s =s8
    t =r10
    m = prohibition
    p = 0
    c = c9+c6+c0+c1+c7+c3+c8
}
one sig rule6 extends Rule{}{
    s =s1
    t =r1
    m = permission
    p = 4
    c = c7+c3+c1+c5+c4+c6+c9
}
one sig rule7 extends Rule{}{
    s =s3
    t =r7
    m = prohibition
    p = 3
    c = c1+c9+c4+c6
}
one sig rule8 extends Rule{}{
    s =s10
    t =r6
    m = prohibition
    p = 4
    c = c5+c6+c3+c1+c2+c9
}
one sig rule9 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 3
    c = c6
}
one sig rule10 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 0
    c = c6+c0+c4+c1+c3
}
one sig rule11 extends Rule{}{
    s =s13
    t =r12
    m = prohibition
    p = 4
    c = c9+c2+c3+c4+c8+c7+c6+c1
}
one sig rule12 extends Rule{}{
    s =s13
    t =r3
    m = permission
    p = 1
    c = c9+c4+c5+c8
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
