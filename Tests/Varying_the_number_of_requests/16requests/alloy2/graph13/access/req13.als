module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s9+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s8+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s4+
         s16->s6+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s14+
         s17->s0+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r2+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r4+
         r7->r6+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r11+
         r13->r3+
         r13->r9+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r6+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r9+
         r18->r10+
         r19->r0+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r13+
         r19->r15+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req13 extends Request{}{
sub=s3
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r15
    m = permission
    p = 4
    c = c3+c6+c8
}
one sig rule1 extends Rule{}{
    s =s12
    t =r12
    m = prohibition
    p = 0
    c = c0+c2+c5+c3+c4
}
one sig rule2 extends Rule{}{
    s =s11
    t =r18
    m = prohibition
    p = 1
    c = c0+c3+c6+c2
}
one sig rule3 extends Rule{}{
    s =s6
    t =r13
    m = prohibition
    p = 2
    c = c2+c6+c8+c5
}
one sig rule4 extends Rule{}{
    s =s13
    t =r8
    m = permission
    p = 1
    c = c7+c4+c9+c3
}
one sig rule5 extends Rule{}{
    s =s12
    t =r2
    m = prohibition
    p = 3
    c = c8+c3+c4
}
one sig rule6 extends Rule{}{
    s =s1
    t =r0
    m = prohibition
    p = 1
    c = c3+c9+c1
}
one sig rule7 extends Rule{}{
    s =s10
    t =r14
    m = prohibition
    p = 0
    c = c6+c4+c9+c7+c8+c3+c1
}
one sig rule8 extends Rule{}{
    s =s12
    t =r2
    m = permission
    p = 1
    c = c0+c1+c4+c3+c9+c6+c7
}
one sig rule9 extends Rule{}{
    s =s19
    t =r2
    m = permission
    p = 3
    c = c3+c5+c6+c4+c7+c8+c1
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
run accessReq13_c0{access_condition[req13,c0]} for 4
run accessReq13_c1{access_condition[req13,c1]} for 4
run accessReq13_c2{access_condition[req13,c2]} for 4
run accessReq13_c3{access_condition[req13,c3]} for 4
run accessReq13_c4{access_condition[req13,c4]} for 4
run accessReq13_c5{access_condition[req13,c5]} for 4
run accessReq13_c6{access_condition[req13,c6]} for 4
run accessReq13_c7{access_condition[req13,c7]} for 4
run accessReq13_c8{access_condition[req13,c8]} for 4
run accessReq13_c9{access_condition[req13,c9]} for 4
