module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s1+
         s7->s4+
         s7->s6}
one sig r0, r1, r2, r3, r4, r5, r6, r7 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r2+
         r7->r3}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 3
    c = c4+c6+c0+c5+c7
}
one sig rule1 extends Rule{}{
    s =s4
    t =r6
    m = prohibition
    p = 4
    c = c3
}
one sig rule2 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 2
    c = c9+c4+c5+c1
}
one sig rule3 extends Rule{}{
    s =s7
    t =r1
    m = permission
    p = 3
    c = c3+c8+c6+c7
}
one sig rule4 extends Rule{}{
    s =s5
    t =r3
    m = prohibition
    p = 0
    c = c7+c3+c9
}
one sig rule5 extends Rule{}{
    s =s7
    t =r3
    m = prohibition
    p = 4
    c = c3+c7+c2+c8+c5
}
one sig rule6 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 4
    c = c5+c3+c9+c0
}
one sig rule7 extends Rule{}{
    s =s4
    t =r4
    m = prohibition
    p = 0
    c = c7+c0+c6
}
one sig rule8 extends Rule{}{
    s =s5
    t =r2
    m = permission
    p = 4
    c = c7+c4+c5+c0
}
one sig rule9 extends Rule{}{
    s =s2
    t =r1
    m = permission
    p = 2
    c = c5+c3+c9+c8
}
one sig rule10 extends Rule{}{
    s =s5
    t =r7
    m = permission
    p = 2
    c = c7
}
one sig rule11 extends Rule{}{
    s =s5
    t =r5
    m = permission
    p = 3
    c = c3+c8+c0+c5+c6
}
one sig rule12 extends Rule{}{
    s =s5
    t =r7
    m = permission
    p = 0
    c = c6+c9
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
run accessReq4_c0{access_condition[req4,c0]} for 4
run accessReq4_c1{access_condition[req4,c1]} for 4
run accessReq4_c2{access_condition[req4,c2]} for 4
run accessReq4_c3{access_condition[req4,c3]} for 4
run accessReq4_c4{access_condition[req4,c4]} for 4
run accessReq4_c5{access_condition[req4,c5]} for 4
run accessReq4_c6{access_condition[req4,c6]} for 4
run accessReq4_c7{access_condition[req4,c7]} for 4
run accessReq4_c8{access_condition[req4,c8]} for 4
run accessReq4_c9{access_condition[req4,c9]} for 4
