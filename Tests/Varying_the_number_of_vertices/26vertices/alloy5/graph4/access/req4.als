module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s2+
         s5->s0+
         s5->s1+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s5+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s7+
         s12->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r2+
         r11->r5+
         r11->r9+
         r12->r2+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 1
    c = c0+c2+c8+c6
}
one sig rule1 extends Rule{}{
    s =s3
    t =r2
    m = permission
    p = 1
    c = c5+c3
}
one sig rule2 extends Rule{}{
    s =s8
    t =r12
    m = prohibition
    p = 2
    c = c2+c7+c5+c0
}
one sig rule3 extends Rule{}{
    s =s4
    t =r7
    m = prohibition
    p = 3
    c = c8+c5+c4+c3+c6+c1+c9
}
one sig rule4 extends Rule{}{
    s =s5
    t =r10
    m = prohibition
    p = 4
    c = c5
}
one sig rule5 extends Rule{}{
    s =s2
    t =r7
    m = prohibition
    p = 0
    c = c3+c1+c9
}
one sig rule6 extends Rule{}{
    s =s8
    t =r1
    m = permission
    p = 0
    c = c1+c2+c6+c4+c5
}
one sig rule7 extends Rule{}{
    s =s12
    t =r11
    m = permission
    p = 0
    c = c1+c7+c4
}
one sig rule8 extends Rule{}{
    s =s4
    t =r11
    m = permission
    p = 0
    c = c4+c6+c9
}
one sig rule9 extends Rule{}{
    s =s8
    t =r5
    m = permission
    p = 1
    c = c3+c6+c8+c4+c5+c1
}
one sig rule10 extends Rule{}{
    s =s0
    t =r10
    m = prohibition
    p = 0
    c = c3+c0+c5
}
one sig rule11 extends Rule{}{
    s =s5
    t =r10
    m = permission
    p = 4
    c = c4+c8+c1+c7+c9+c5
}
one sig rule12 extends Rule{}{
    s =s5
    t =r8
    m = prohibition
    p = 0
    c = c2
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
