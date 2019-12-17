module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s2+
         s4->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s7+
         s9->s2+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s6+
         s11->s7+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s9+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s6+
         s16->s9+
         s16->s12+
         s16->s13+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s11+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s16+
         s18->s17+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r1+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r4+
         r9->r1+
         r9->r3+
         r9->r5+
         r9->r6+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r8+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r11+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r15+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r3
    m = prohibition
    p = 1
    c = c4+c6+c0
}
one sig rule1 extends Rule{}{
    s =s4
    t =r11
    m = permission
    p = 1
    c = c7+c9+c4
}
one sig rule2 extends Rule{}{
    s =s4
    t =r16
    m = permission
    p = 3
    c = c0+c8+c5+c9+c7+c2+c1
}
one sig rule3 extends Rule{}{
    s =s19
    t =r4
    m = permission
    p = 0
    c = c9+c8+c3+c0
}
one sig rule4 extends Rule{}{
    s =s9
    t =r19
    m = permission
    p = 4
    c = c0+c7+c6+c4+c1+c2
}
one sig rule5 extends Rule{}{
    s =s16
    t =r13
    m = prohibition
    p = 3
    c = c8+c1+c4
}
one sig rule6 extends Rule{}{
    s =s3
    t =r7
    m = permission
    p = 0
    c = c7+c0+c5+c6+c4+c9+c2
}
one sig rule7 extends Rule{}{
    s =s4
    t =r3
    m = permission
    p = 0
    c = c2+c0
}
one sig rule8 extends Rule{}{
    s =s16
    t =r2
    m = permission
    p = 4
    c = c9+c7
}
one sig rule9 extends Rule{}{
    s =s15
    t =r19
    m = prohibition
    p = 1
    c = c0+c6+c8+c4+c3+c9
}
one sig rule10 extends Rule{}{
    s =s12
    t =r9
    m = permission
    p = 1
    c = c6+c8+c0+c3+c7+c5+c1
}
one sig rule11 extends Rule{}{
    s =s5
    t =r14
    m = prohibition
    p = 1
    c = c8
}
one sig rule12 extends Rule{}{
    s =s12
    t =r8
    m = permission
    p = 3
    c = c0+c6+c7+c5+c2+c4
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
