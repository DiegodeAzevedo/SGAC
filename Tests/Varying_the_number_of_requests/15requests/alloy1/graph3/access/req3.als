module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s1+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s8->s3+
         s8->s5+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s6+
         s13->s11+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s8+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s4+
         s16->s6+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r2+
         r5->r0+
         r5->r3+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r8->r2+
         r8->r3+
         r8->r4+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r4+
         r10->r1+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r10+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r6+
         r18->r0+
         r18->r1+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r5+
         r19->r7+
         r19->r11+
         r19->r14+
         r19->r16}

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
    s =s14
    t =r10
    m = prohibition
    p = 2
    c = c4+c8+c7+c2+c9+c1
}
one sig rule1 extends Rule{}{
    s =s0
    t =r19
    m = prohibition
    p = 0
    c = c8+c5+c3+c7+c9+c6
}
one sig rule2 extends Rule{}{
    s =s16
    t =r8
    m = prohibition
    p = 0
    c = c1+c0+c7+c9+c3+c8+c6
}
one sig rule3 extends Rule{}{
    s =s13
    t =r6
    m = prohibition
    p = 2
    c = c7+c1+c3+c8+c0+c2
}
one sig rule4 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 3
    c = c9+c2
}
one sig rule5 extends Rule{}{
    s =s14
    t =r7
    m = prohibition
    p = 2
    c = c5+c7+c9+c0+c3+c1
}
one sig rule6 extends Rule{}{
    s =s11
    t =r9
    m = permission
    p = 0
    c = c0
}
one sig rule7 extends Rule{}{
    s =s15
    t =r13
    m = prohibition
    p = 1
    c = c8+c9+c5
}
one sig rule8 extends Rule{}{
    s =s8
    t =r3
    m = prohibition
    p = 4
    c = c5+c4+c2+c7+c8
}
one sig rule9 extends Rule{}{
    s =s11
    t =r7
    m = prohibition
    p = 0
    c = c6+c2+c7+c8+c4
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
