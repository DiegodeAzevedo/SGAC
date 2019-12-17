module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s4+
         s7->s3+
         s7->s4+
         s8->s2+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s0+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s2+
         s14->s4+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s14+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r2+
         r5->r1+
         r5->r4+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r1+
         r8->r2+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r9+
         r12->r10+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r11+
         r16->r12+
         r17->r0+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r7+
         r18->r9+
         r18->r12+
         r18->r13+
         r18->r14+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r8+
         r19->r9+
         r19->r13+
         r19->r14+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r0
    m = permission
    p = 2
    c = c2+c3+c4+c6+c5
}
one sig rule1 extends Rule{}{
    s =s16
    t =r19
    m = prohibition
    p = 0
    c = c4+c2+c8+c3+c5+c9
}
one sig rule2 extends Rule{}{
    s =s7
    t =r11
    m = permission
    p = 2
    c = c9+c0+c2+c6+c4+c5
}
one sig rule3 extends Rule{}{
    s =s10
    t =r9
    m = prohibition
    p = 1
    c = c9+c7+c1
}
one sig rule4 extends Rule{}{
    s =s0
    t =r12
    m = permission
    p = 2
    c = c6+c2+c5+c9+c1+c3
}
one sig rule5 extends Rule{}{
    s =s5
    t =r9
    m = permission
    p = 1
    c = c4+c2+c6
}
one sig rule6 extends Rule{}{
    s =s19
    t =r7
    m = prohibition
    p = 1
    c = c0+c7+c4+c3
}
one sig rule7 extends Rule{}{
    s =s6
    t =r17
    m = prohibition
    p = 0
    c = c8+c1+c5
}
one sig rule8 extends Rule{}{
    s =s8
    t =r0
    m = prohibition
    p = 2
    c = c2+c6
}
one sig rule9 extends Rule{}{
    s =s15
    t =r2
    m = prohibition
    p = 1
    c = c5+c8+c1+c0+c2
}
one sig rule10 extends Rule{}{
    s =s10
    t =r13
    m = prohibition
    p = 0
    c = c4+c5+c7+c1+c3
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
