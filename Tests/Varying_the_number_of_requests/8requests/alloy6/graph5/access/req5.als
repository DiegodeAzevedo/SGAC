module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s4->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s1+
         s9->s3+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s9+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s6+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s15+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r3+
         r6->r0+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r6+
         r9->r2+
         r9->r3+
         r9->r4+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r12+
         r15->r0+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r6+
         r17->r7+
         r17->r11+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s2
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r14
    m = permission
    p = 3
    c = c3+c6+c9+c2+c1
}
one sig rule1 extends Rule{}{
    s =s13
    t =r5
    m = prohibition
    p = 3
    c = c3+c0+c8+c5
}
one sig rule2 extends Rule{}{
    s =s6
    t =r17
    m = prohibition
    p = 4
    c = c8+c0+c6+c2+c4+c1
}
one sig rule3 extends Rule{}{
    s =s12
    t =r3
    m = prohibition
    p = 2
    c = c8+c6+c0+c2+c7+c4
}
one sig rule4 extends Rule{}{
    s =s15
    t =r2
    m = permission
    p = 2
    c = c2+c5
}
one sig rule5 extends Rule{}{
    s =s19
    t =r0
    m = prohibition
    p = 4
    c = c8+c9+c1
}
one sig rule6 extends Rule{}{
    s =s3
    t =r11
    m = permission
    p = 1
    c = c9+c5+c3+c6
}
one sig rule7 extends Rule{}{
    s =s10
    t =r2
    m = prohibition
    p = 4
    c = c1+c8+c6+c0+c9+c2
}
one sig rule8 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 3
    c = c7+c4+c8+c5+c3+c9+c1
}
one sig rule9 extends Rule{}{
    s =s14
    t =r2
    m = prohibition
    p = 4
    c = c8+c4+c2+c3+c6+c9+c1
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
