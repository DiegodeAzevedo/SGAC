module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s4->s1+
         s4->s2+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s3+
         s7->s4+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s11+
         s14->s1+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s9+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s6+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s8+
         s18->s10+
         s18->s13+
         s18->s14+
         s19->s3+
         s19->s4+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r1+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r6+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r9+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req8 extends Request{}{
sub=s3
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r19
    m = prohibition
    p = 1
    c = c5+c0+c7+c1
}
one sig rule1 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 2
    c = c0+c7+c5
}
one sig rule2 extends Rule{}{
    s =s3
    t =r6
    m = permission
    p = 0
    c = c9
}
one sig rule3 extends Rule{}{
    s =s3
    t =r7
    m = prohibition
    p = 3
    c = c9+c7+c0+c8+c5+c3
}
one sig rule4 extends Rule{}{
    s =s11
    t =r17
    m = permission
    p = 3
    c = c0+c1+c7+c9+c5+c2+c6
}
one sig rule5 extends Rule{}{
    s =s19
    t =r17
    m = prohibition
    p = 4
    c = c8+c4+c2+c6+c5+c9
}
one sig rule6 extends Rule{}{
    s =s14
    t =r12
    m = prohibition
    p = 2
    c = c8+c4+c2+c6
}
one sig rule7 extends Rule{}{
    s =s13
    t =r4
    m = permission
    p = 2
    c = c5+c2+c7+c6+c0
}
one sig rule8 extends Rule{}{
    s =s13
    t =r12
    m = prohibition
    p = 0
    c = c1
}
one sig rule9 extends Rule{}{
    s =s0
    t =r12
    m = prohibition
    p = 1
    c = c4+c2
}
one sig rule10 extends Rule{}{
    s =s15
    t =r11
    m = permission
    p = 1
    c = c9+c6+c4
}
one sig rule11 extends Rule{}{
    s =s12
    t =r18
    m = permission
    p = 2
    c = c3+c4+c9+c5
}
one sig rule12 extends Rule{}{
    s =s13
    t =r2
    m = prohibition
    p = 3
    c = c7+c5+c0
}
one sig rule13 extends Rule{}{
    s =s6
    t =r11
    m = prohibition
    p = 3
    c = c4+c7+c3+c6+c8
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
run accessReq8_c0{access_condition[req8,c0]} for 4
run accessReq8_c1{access_condition[req8,c1]} for 4
run accessReq8_c2{access_condition[req8,c2]} for 4
run accessReq8_c3{access_condition[req8,c3]} for 4
run accessReq8_c4{access_condition[req8,c4]} for 4
run accessReq8_c5{access_condition[req8,c5]} for 4
run accessReq8_c6{access_condition[req8,c6]} for 4
run accessReq8_c7{access_condition[req8,c7]} for 4
run accessReq8_c8{access_condition[req8,c8]} for 4
run accessReq8_c9{access_condition[req8,c9]} for 4
