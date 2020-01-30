module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s4->s0+
         s4->s1+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s6+
         s8->s2+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s10->s0+
         s10->s2+
         s10->s6+
         s10->s9+
         s11->s3+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s7+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s11+
         s18->s14+
         s18->s16+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r4->r2+
         r4->r3+
         r5->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r7+
         r10->r0+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r3+
         r12->r4+
         r12->r8+
         r12->r11+
         r13->r3+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r9+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r6+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r6
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r3
    m = permission
    p = 0
    c = c5+c9+c3+c4
}
one sig rule1 extends Rule{}{
    s =s13
    t =r10
    m = prohibition
    p = 2
    c = c6
}
one sig rule2 extends Rule{}{
    s =s0
    t =r2
    m = prohibition
    p = 0
    c = c5+c2+c4+c1
}
one sig rule3 extends Rule{}{
    s =s12
    t =r7
    m = permission
    p = 4
    c = c9+c3+c8+c5
}
one sig rule4 extends Rule{}{
    s =s6
    t =r11
    m = permission
    p = 0
    c = c2
}
one sig rule5 extends Rule{}{
    s =s2
    t =r8
    m = prohibition
    p = 0
    c = c4+c3+c5
}
one sig rule6 extends Rule{}{
    s =s5
    t =r6
    m = permission
    p = 3
    c = c5+c7+c8+c6
}
one sig rule7 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 3
    c = c0+c2
}
one sig rule8 extends Rule{}{
    s =s18
    t =r16
    m = prohibition
    p = 4
    c = c4
}
one sig rule9 extends Rule{}{
    s =s15
    t =r3
    m = prohibition
    p = 1
    c = c7+c3+c6+c2+c1
}
one sig rule10 extends Rule{}{
    s =s7
    t =r4
    m = prohibition
    p = 0
    c = c1+c6+c3+c0
}
one sig rule11 extends Rule{}{
    s =s9
    t =r10
    m = permission
    p = 1
    c = c1+c7+c9+c2+c8+c0+c3
}
one sig rule12 extends Rule{}{
    s =s3
    t =r5
    m = permission
    p = 4
    c = c8+c2+c5+c1+c6+c4
}
one sig rule13 extends Rule{}{
    s =s19
    t =r13
    m = permission
    p = 3
    c = c0+c5+c8+c1+c7+c2
}
one sig rule14 extends Rule{}{
    s =s4
    t =r0
    m = permission
    p = 0
    c = c4+c6+c5+c2+c9+c8
}
one sig rule15 extends Rule{}{
    s =s3
    t =r9
    m = permission
    p = 2
    c = c1+c3+c0+c7+c6
}
one sig rule16 extends Rule{}{
    s =s14
    t =r8
    m = prohibition
    p = 1
    c = c6+c5+c4+c7+c0+c1+c3
}
one sig rule17 extends Rule{}{
    s =s12
    t =r9
    m = prohibition
    p = 2
    c = c3
}
one sig rule18 extends Rule{}{
    s =s15
    t =r19
    m = prohibition
    p = 3
    c = c7+c0+c9+c3+c6+c2+c4
}
one sig rule19 extends Rule{}{
    s =s14
    t =r12
    m = permission
    p = 2
    c = c2+c5+c0+c3
}
one sig rule20 extends Rule{}{
    s =s3
    t =r18
    m = permission
    p = 3
    c = c0+c3+c5
}
one sig rule21 extends Rule{}{
    s =s1
    t =r14
    m = prohibition
    p = 1
    c = c5+c8
}
one sig rule22 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 0
    c = c5+c9+c6
}
one sig rule23 extends Rule{}{
    s =s6
    t =r10
    m = prohibition
    p = 0
    c = c9+c0+c6+c5+c3+c8
}
one sig rule24 extends Rule{}{
    s =s10
    t =r4
    m = prohibition
    p = 1
    c = c6+c1+c4
}
one sig rule25 extends Rule{}{
    s =s7
    t =r12
    m = prohibition
    p = 1
    c = c3+c8+c7+c6+c0
}
one sig rule26 extends Rule{}{
    s =s13
    t =r18
    m = permission
    p = 3
    c = c5+c3+c8+c7+c6+c9
}
one sig rule27 extends Rule{}{
    s =s12
    t =r1
    m = permission
    p = 2
    c = c6+c2+c5
}
one sig rule28 extends Rule{}{
    s =s6
    t =r17
    m = prohibition
    p = 0
    c = c5+c7+c2+c8
}
one sig rule29 extends Rule{}{
    s =s19
    t =r16
    m = prohibition
    p = 2
    c = c0+c6+c4
}
one sig rule30 extends Rule{}{
    s =s11
    t =r19
    m = prohibition
    p = 3
    c = c2+c8+c3+c5
}
one sig rule31 extends Rule{}{
    s =s2
    t =r12
    m = prohibition
    p = 4
    c = c5
}
one sig rule32 extends Rule{}{
    s =s14
    t =r10
    m = permission
    p = 0
    c = c3+c4+c5+c6+c2+c1
}
one sig rule33 extends Rule{}{
    s =s18
    t =r2
    m = prohibition
    p = 2
    c = c8+c4+c1+c6+c0
}
one sig rule34 extends Rule{}{
    s =s2
    t =r5
    m = prohibition
    p = 1
    c = c1+c8
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
run accessReq1_c0{access_condition[req1,c0]} for 4
run accessReq1_c1{access_condition[req1,c1]} for 4
run accessReq1_c2{access_condition[req1,c2]} for 4
run accessReq1_c3{access_condition[req1,c3]} for 4
run accessReq1_c4{access_condition[req1,c4]} for 4
run accessReq1_c5{access_condition[req1,c5]} for 4
run accessReq1_c6{access_condition[req1,c6]} for 4
run accessReq1_c7{access_condition[req1,c7]} for 4
run accessReq1_c8{access_condition[req1,c8]} for 4
run accessReq1_c9{access_condition[req1,c9]} for 4
