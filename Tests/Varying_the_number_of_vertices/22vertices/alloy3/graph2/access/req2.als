module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s1+
         s4->s2+
         s5->s3+
         s6->s0+
         s6->s2+
         s6->s3+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r2+
         r4->r0+
         r5->r0+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r3+
         r7->r5+
         r8->r2+
         r8->r5+
         r9->r0+
         r9->r5+
         r9->r8+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r8}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s9
    t =r0
    m = permission
    p = 1
    c = c5+c0+c1+c4+c9
}
one sig rule1 extends Rule{}{
    s =s7
    t =r3
    m = permission
    p = 0
    c = c8
}
one sig rule2 extends Rule{}{
    s =s10
    t =r8
    m = prohibition
    p = 3
    c = c7+c5+c6+c1+c3
}
one sig rule3 extends Rule{}{
    s =s5
    t =r4
    m = permission
    p = 4
    c = c0
}
one sig rule4 extends Rule{}{
    s =s10
    t =r2
    m = prohibition
    p = 3
    c = c3+c6
}
one sig rule5 extends Rule{}{
    s =s0
    t =r1
    m = permission
    p = 1
    c = c9+c8+c5
}
one sig rule6 extends Rule{}{
    s =s8
    t =r1
    m = permission
    p = 2
    c = c6+c7+c5+c0
}
one sig rule7 extends Rule{}{
    s =s5
    t =r5
    m = prohibition
    p = 4
    c = c0+c8+c2+c3+c9
}
one sig rule8 extends Rule{}{
    s =s6
    t =r0
    m = prohibition
    p = 2
    c = c4+c7+c2+c9+c1+c6+c0
}
one sig rule9 extends Rule{}{
    s =s6
    t =r1
    m = prohibition
    p = 2
    c = c0+c1+c8+c4+c5
}
one sig rule10 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 0
    c = c3+c9+c2+c8+c4+c5+c0
}
one sig rule11 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 0
    c = c3+c6+c9+c2+c0+c7+c8
}
one sig rule12 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 4
    c = c6+c1+c7+c3+c5+c9
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
