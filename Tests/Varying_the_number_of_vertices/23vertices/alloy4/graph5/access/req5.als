module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11 extends Subject{}{}
fact{
subSucc=s2->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s4+
         s9->s6+
         s9->s7+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s5+
         s11->s1+
         s11->s3+
         s11->s9+
         s11->s10}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r5->r0+
         r5->r1+
         r5->r4+
         r6->r3+
         r6->r4+
         r7->r5+
         r8->r3+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r6}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s1
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 0
    c = c4
}
one sig rule1 extends Rule{}{
    s =s3
    t =r0
    m = prohibition
    p = 4
    c = c2+c7+c1
}
one sig rule2 extends Rule{}{
    s =s6
    t =r4
    m = prohibition
    p = 4
    c = c5+c7+c0+c2+c9
}
one sig rule3 extends Rule{}{
    s =s8
    t =r7
    m = permission
    p = 3
    c = c8+c6+c4+c5+c0+c1
}
one sig rule4 extends Rule{}{
    s =s2
    t =r0
    m = prohibition
    p = 1
    c = c2+c4+c8+c7+c6+c9
}
one sig rule5 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 2
    c = c5+c7+c6+c3
}
one sig rule6 extends Rule{}{
    s =s7
    t =r10
    m = prohibition
    p = 3
    c = c5+c7+c0+c6+c1
}
one sig rule7 extends Rule{}{
    s =s5
    t =r5
    m = prohibition
    p = 3
    c = c8+c7+c6+c2
}
one sig rule8 extends Rule{}{
    s =s7
    t =r4
    m = permission
    p = 4
    c = c5
}
one sig rule9 extends Rule{}{
    s =s7
    t =r6
    m = prohibition
    p = 2
    c = c7+c4
}
one sig rule10 extends Rule{}{
    s =s4
    t =r0
    m = prohibition
    p = 2
    c = c3
}
one sig rule11 extends Rule{}{
    s =s9
    t =r3
    m = permission
    p = 4
    c = c9+c3+c2
}
one sig rule12 extends Rule{}{
    s =s5
    t =r5
    m = permission
    p = 1
    c = c2+c5
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
run accessReq5_c0{access_condition[req5,c0]} for 4
run accessReq5_c1{access_condition[req5,c1]} for 4
run accessReq5_c2{access_condition[req5,c2]} for 4
run accessReq5_c3{access_condition[req5,c3]} for 4
run accessReq5_c4{access_condition[req5,c4]} for 4
run accessReq5_c5{access_condition[req5,c5]} for 4
run accessReq5_c6{access_condition[req5,c6]} for 4
run accessReq5_c7{access_condition[req5,c7]} for 4
run accessReq5_c8{access_condition[req5,c8]} for 4
run accessReq5_c9{access_condition[req5,c9]} for 4
