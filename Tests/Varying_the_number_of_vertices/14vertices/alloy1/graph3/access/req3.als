module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6 extends Subject{}{}
fact{
subSucc=s1->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s6->s2+
         s6->s3+
         s6->s5}
one sig r0, r1, r2, r3, r4, r5, r6 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r3+
         r6->r4+
         r6->r5}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s2
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 0
    c = c1+c3+c5+c0+c2
}
one sig rule1 extends Rule{}{
    s =s0
    t =r6
    m = permission
    p = 1
    c = c4+c1
}
one sig rule2 extends Rule{}{
    s =s5
    t =r2
    m = permission
    p = 3
    c = c2+c3
}
one sig rule3 extends Rule{}{
    s =s3
    t =r1
    m = permission
    p = 1
    c = c7+c8+c4+c9
}
one sig rule4 extends Rule{}{
    s =s0
    t =r5
    m = permission
    p = 3
    c = c0+c9+c1+c4
}
one sig rule5 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 3
    c = c5+c1+c9+c6+c2
}
one sig rule6 extends Rule{}{
    s =s6
    t =r2
    m = permission
    p = 1
    c = c8+c2+c6
}
one sig rule7 extends Rule{}{
    s =s0
    t =r6
    m = prohibition
    p = 4
    c = c7+c9
}
one sig rule8 extends Rule{}{
    s =s1
    t =r2
    m = prohibition
    p = 3
    c = c2+c9+c3+c1+c5
}
one sig rule9 extends Rule{}{
    s =s4
    t =r6
    m = permission
    p = 0
    c = c4+c9+c0+c3+c1
}
one sig rule10 extends Rule{}{
    s =s6
    t =r0
    m = permission
    p = 0
    c = c7+c6+c8+c1+c2
}
one sig rule11 extends Rule{}{
    s =s0
    t =r4
    m = prohibition
    p = 4
    c = c4+c8+c9+c5+c3+c6
}
one sig rule12 extends Rule{}{
    s =s5
    t =r2
    m = permission
    p = 0
    c = c8+c2+c3+c1
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
