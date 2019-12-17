module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s9+
         s11->s10}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r5->r1+
         r5->r3+
         r6->r1+
         r6->r2+
         r7->r6+
         r8->r2+
         r8->r3+
         r8->r4+
         r9->r2+
         r9->r7+
         r9->r8+
         r10->r4+
         r10->r6}

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
    s =s1
    t =r7
    m = permission
    p = 0
    c = c3+c1
}
one sig rule1 extends Rule{}{
    s =s3
    t =r7
    m = permission
    p = 2
    c = c9+c4+c1+c5
}
one sig rule2 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 0
    c = c2+c6+c1+c7+c3+c4+c0
}
one sig rule3 extends Rule{}{
    s =s3
    t =r4
    m = permission
    p = 2
    c = c5+c8+c3+c0+c6+c9
}
one sig rule4 extends Rule{}{
    s =s10
    t =r7
    m = permission
    p = 1
    c = c2+c4+c6+c1
}
one sig rule5 extends Rule{}{
    s =s0
    t =r6
    m = permission
    p = 2
    c = c8+c6
}
one sig rule6 extends Rule{}{
    s =s1
    t =r10
    m = prohibition
    p = 1
    c = c3+c9+c2
}
one sig rule7 extends Rule{}{
    s =s0
    t =r1
    m = permission
    p = 2
    c = c2
}
one sig rule8 extends Rule{}{
    s =s8
    t =r9
    m = permission
    p = 1
    c = c4+c6+c2+c5
}
one sig rule9 extends Rule{}{
    s =s6
    t =r1
    m = prohibition
    p = 0
    c = c3+c6
}
one sig rule10 extends Rule{}{
    s =s1
    t =r7
    m = permission
    p = 3
    c = c4+c6+c3+c8+c0+c2
}
one sig rule11 extends Rule{}{
    s =s4
    t =r10
    m = prohibition
    p = 3
    c = c1+c6
}
one sig rule12 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 4
    c = c7+c1+c2+c6
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
