module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s4->s0+
         s4->s1+
         s4->s3}
one sig r0, r1, r2, r3, r4 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r2}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 0
    c = c8+c1+c0+c6+c3+c4
}
one sig rule1 extends Rule{}{
    s =s1
    t =r0
    m = prohibition
    p = 2
    c = c0+c1+c6+c4
}
one sig rule2 extends Rule{}{
    s =s3
    t =r0
    m = permission
    p = 4
    c = c4+c6+c9+c7
}
one sig rule3 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 3
    c = c0+c8+c6+c5+c3+c7
}
one sig rule4 extends Rule{}{
    s =s4
    t =r4
    m = permission
    p = 2
    c = c8+c3+c5+c1
}
one sig rule5 extends Rule{}{
    s =s0
    t =r4
    m = prohibition
    p = 0
    c = c5+c0
}
one sig rule6 extends Rule{}{
    s =s3
    t =r2
    m = prohibition
    p = 3
    c = c4+c5+c3+c1
}
one sig rule7 extends Rule{}{
    s =s3
    t =r4
    m = prohibition
    p = 0
    c = c0+c1+c5+c4+c7
}
one sig rule8 extends Rule{}{
    s =s4
    t =r2
    m = prohibition
    p = 4
    c = c2+c4+c5+c3+c9
}
one sig rule9 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 2
    c = c8+c6+c3
}
one sig rule10 extends Rule{}{
    s =s0
    t =r3
    m = permission
    p = 1
    c = c8+c0+c4+c6+c7+c1
}
one sig rule11 extends Rule{}{
    s =s1
    t =r0
    m = permission
    p = 1
    c = c9+c8+c5+c2
}
one sig rule12 extends Rule{}{
    s =s4
    t =r1
    m = prohibition
    p = 1
    c = c3+c1+c4+c7+c0
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
run accessReq3_c0{access_condition[req3,c0]} for 4
run accessReq3_c1{access_condition[req3,c1]} for 4
run accessReq3_c2{access_condition[req3,c2]} for 4
run accessReq3_c3{access_condition[req3,c3]} for 4
run accessReq3_c4{access_condition[req3,c4]} for 4
run accessReq3_c5{access_condition[req3,c5]} for 4
run accessReq3_c6{access_condition[req3,c6]} for 4
run accessReq3_c7{access_condition[req3,c7]} for 4
run accessReq3_c8{access_condition[req3,c8]} for 4
run accessReq3_c9{access_condition[req3,c9]} for 4
