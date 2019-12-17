module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s4+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s3+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s5+
         s9->s7+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s4+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s12+
         s16->s2+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s15+
         s17->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r8+
         r11->r1+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r8+
         r15->r9+
         r15->r13+
         r16->r2+
         r16->r3+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r14+
         r16->r15}

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
    s =s1
    t =r2
    m = permission
    p = 1
    c = c1
}
one sig rule1 extends Rule{}{
    s =s0
    t =r16
    m = permission
    p = 0
    c = c8+c3+c2+c9+c5
}
one sig rule2 extends Rule{}{
    s =s10
    t =r8
    m = permission
    p = 0
    c = c4+c6+c2+c0+c3+c7
}
one sig rule3 extends Rule{}{
    s =s9
    t =r6
    m = prohibition
    p = 3
    c = c0+c3+c9+c4+c2+c6
}
one sig rule4 extends Rule{}{
    s =s4
    t =r15
    m = permission
    p = 2
    c = c1+c0+c7+c4
}
one sig rule5 extends Rule{}{
    s =s2
    t =r1
    m = permission
    p = 2
    c = c5+c7+c9+c8+c3+c0
}
one sig rule6 extends Rule{}{
    s =s13
    t =r8
    m = prohibition
    p = 0
    c = c0+c7
}
one sig rule7 extends Rule{}{
    s =s1
    t =r15
    m = prohibition
    p = 4
    c = c1+c0
}
one sig rule8 extends Rule{}{
    s =s17
    t =r1
    m = prohibition
    p = 4
    c = c6+c4
}
one sig rule9 extends Rule{}{
    s =s4
    t =r6
    m = prohibition
    p = 3
    c = c2+c6+c4+c7+c5+c3+c1
}
one sig rule10 extends Rule{}{
    s =s0
    t =r9
    m = permission
    p = 1
    c = c3
}
one sig rule11 extends Rule{}{
    s =s13
    t =r2
    m = prohibition
    p = 4
    c = c7
}
one sig rule12 extends Rule{}{
    s =s1
    t =r2
    m = permission
    p = 0
    c = c6+c7+c2+c4+c8+c3+c0
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
