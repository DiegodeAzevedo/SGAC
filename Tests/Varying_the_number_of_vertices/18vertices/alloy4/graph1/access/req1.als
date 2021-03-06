module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8 extends Subject{}{}
fact{
subSucc=s2->s0+
         s4->s0+
         s4->s2+
         s6->s1+
         s6->s2+
         s6->s5+
         s7->s0+
         s7->s3+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8 extends Resource{}{}
fact{
resSucc=r2->r1+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r3+
         r8->r5}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 4
    c = c4+c6+c3+c5+c9
}
one sig rule1 extends Rule{}{
    s =s7
    t =r5
    m = permission
    p = 0
    c = c6+c4+c8+c3
}
one sig rule2 extends Rule{}{
    s =s8
    t =r8
    m = prohibition
    p = 0
    c = c8+c6+c7+c9+c4+c5
}
one sig rule3 extends Rule{}{
    s =s5
    t =r2
    m = prohibition
    p = 0
    c = c7+c5+c0+c9+c3
}
one sig rule4 extends Rule{}{
    s =s5
    t =r2
    m = prohibition
    p = 4
    c = c8+c5+c2+c0+c4+c1+c3
}
one sig rule5 extends Rule{}{
    s =s4
    t =r5
    m = permission
    p = 2
    c = c8+c1
}
one sig rule6 extends Rule{}{
    s =s8
    t =r6
    m = permission
    p = 0
    c = c3+c8+c2
}
one sig rule7 extends Rule{}{
    s =s1
    t =r4
    m = permission
    p = 4
    c = c8+c4
}
one sig rule8 extends Rule{}{
    s =s5
    t =r5
    m = permission
    p = 2
    c = c4+c8+c3+c2
}
one sig rule9 extends Rule{}{
    s =s3
    t =r4
    m = prohibition
    p = 0
    c = c6+c0
}
one sig rule10 extends Rule{}{
    s =s1
    t =r0
    m = permission
    p = 2
    c = c1+c7+c5+c3
}
one sig rule11 extends Rule{}{
    s =s6
    t =r8
    m = permission
    p = 4
    c = c0+c3+c9+c6+c8+c2
}
one sig rule12 extends Rule{}{
    s =s5
    t =r7
    m = permission
    p = 4
    c = c4+c7+c1+c6+c8+c9+c2+c5
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
