module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s4->s0+
         s4->s2+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s5+
         s10->s0+
         s10->s7+
         s10->s9+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s5+
         s13->s10+
         s13->s11+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s4+
         s16->s8+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s4+
         s17->s9+
         s17->s11+
         s17->s14+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s12+
         s18->s14+
         s18->s15+
         s19->s3+
         s19->s6+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r4->r1+
         r4->r3+
         r5->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r8->r1+
         r8->r2+
         r8->r3+
         r9->r0+
         r9->r2+
         r9->r3+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r5+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r8+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r11+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r13+
         r18->r0+
         r18->r2+
         r18->r8+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r7+
         r19->r8}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r14
    m = permission
    p = 2
    c = c1+c6+c7+c5
}
one sig rule1 extends Rule{}{
    s =s8
    t =r3
    m = permission
    p = 1
    c = c2+c0+c6+c1+c7
}
one sig rule2 extends Rule{}{
    s =s17
    t =r14
    m = permission
    p = 4
    c = c1+c6+c7+c4+c8+c9+c2
}
one sig rule3 extends Rule{}{
    s =s8
    t =r10
    m = prohibition
    p = 1
    c = c0+c5+c1+c9+c6
}
one sig rule4 extends Rule{}{
    s =s14
    t =r16
    m = permission
    p = 4
    c = c4+c7+c0
}
one sig rule5 extends Rule{}{
    s =s16
    t =r16
    m = prohibition
    p = 1
    c = c7+c9+c5+c6+c8+c1
}
one sig rule6 extends Rule{}{
    s =s18
    t =r8
    m = permission
    p = 3
    c = c7+c6+c9+c4+c0+c5
}
one sig rule7 extends Rule{}{
    s =s14
    t =r15
    m = prohibition
    p = 1
    c = c8+c6
}
one sig rule8 extends Rule{}{
    s =s14
    t =r12
    m = prohibition
    p = 1
    c = c9+c8+c0+c4+c3
}
one sig rule9 extends Rule{}{
    s =s4
    t =r6
    m = permission
    p = 2
    c = c0+c6+c7+c3+c9+c1
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
run accessReq5_c0{access_condition[req5,c0]} for 4
run accessReq5_c1{access_condition[req5,c1]} for 4
run accessReq5_c2{access_condition[req5,c2]} for 4
run accessReq5_c3{access_condition[req5,c3]} for 4
run accessReq5_c4{access_condition[req5,c4]} for 4
run accessReq5_c5{access_condition[req5,c5]} for 4
run accessReq5_c6{access_condition[req5,c6]} for 4
run accessReq5_c7{access_condition[req5,c7]} for 4
run accessReq5_c8{access_condition[req5,c8]} for 4
run accessReq5_c9{access_condition[req5,c9]} for 4
