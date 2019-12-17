module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4}
one sig r0, r1, r2, r3, r4 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r3->r2+
         r4->r2}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 3
    c = c3+c1+c5+c9
}
one sig rule1 extends Rule{}{
    s =s0
    t =r0
    m = prohibition
    p = 4
    c = c9+c0+c6+c1+c3
}
one sig rule2 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 0
    c = c3+c4+c6+c9+c8
}
one sig rule3 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 3
    c = c9+c7+c4+c6+c1+c8+c0+c3
}
one sig rule4 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 4
    c = c2+c6
}
one sig rule5 extends Rule{}{
    s =s0
    t =r3
    m = permission
    p = 0
    c = c4+c7+c9+c3+c5+c8+c2
}
one sig rule6 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 1
    c = c7+c0+c1+c9+c8+c5+c3
}
one sig rule7 extends Rule{}{
    s =s4
    t =r0
    m = permission
    p = 2
    c = c9+c8+c2
}
one sig rule8 extends Rule{}{
    s =s0
    t =r2
    m = prohibition
    p = 4
    c = c4+c1+c6+c3+c9+c0+c8+c2
}
one sig rule9 extends Rule{}{
    s =s0
    t =r4
    m = prohibition
    p = 4
    c = c2
}
one sig rule10 extends Rule{}{
    s =s2
    t =r2
    m = permission
    p = 4
    c = c1+c0
}
one sig rule11 extends Rule{}{
    s =s2
    t =r3
    m = prohibition
    p = 4
    c = c0+c4+c3+c9+c6
}
one sig rule12 extends Rule{}{
    s =s2
    t =r1
    m = permission
    p = 4
    c = c3+c0+c4+c1+c5+c8
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
