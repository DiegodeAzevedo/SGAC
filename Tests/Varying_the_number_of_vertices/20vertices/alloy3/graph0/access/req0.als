module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s6+
         s9->s7}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r2+
         r4->r1+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r4+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r2}

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
    t =r1
    m = permission
    p = 1
    c = c2+c8+c1+c6+c5+c0+c7
}
one sig rule1 extends Rule{}{
    s =s6
    t =r4
    m = permission
    p = 1
    c = c5+c7+c6+c2+c1
}
one sig rule2 extends Rule{}{
    s =s4
    t =r2
    m = prohibition
    p = 0
    c = c6+c8+c1
}
one sig rule3 extends Rule{}{
    s =s3
    t =r2
    m = prohibition
    p = 0
    c = c9+c7+c8+c1
}
one sig rule4 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 2
    c = c3+c6
}
one sig rule5 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 0
    c = c9+c7+c2+c0+c1+c5
}
one sig rule6 extends Rule{}{
    s =s1
    t =r9
    m = permission
    p = 2
    c = c3+c4+c7
}
one sig rule7 extends Rule{}{
    s =s0
    t =r3
    m = prohibition
    p = 2
    c = c8+c4+c1+c2+c9
}
one sig rule8 extends Rule{}{
    s =s7
    t =r0
    m = permission
    p = 1
    c = c8
}
one sig rule9 extends Rule{}{
    s =s0
    t =r2
    m = permission
    p = 4
    c = c5+c7+c4+c9+c1+c8+c6
}
one sig rule10 extends Rule{}{
    s =s0
    t =r8
    m = prohibition
    p = 0
    c = c7+c4+c9+c1
}
one sig rule11 extends Rule{}{
    s =s9
    t =r9
    m = prohibition
    p = 1
    c = c1
}
one sig rule12 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 2
    c = c4+c2+c6
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
