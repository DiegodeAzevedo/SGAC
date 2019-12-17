module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s2+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s7+
         s12->s0+
         s12->s2+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s12+
         s18->s13+
         s18->s15+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s12+
         s19->s14+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r7->r0+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r4+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r7+
         r12->r10+
         r13->r0+
         r13->r4+
         r13->r5+
         r14->r2+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r12+
         r15->r14+
         r16->r2+
         r16->r4+
         r16->r11+
         r16->r12+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r15+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r13+
         r19->r0+
         r19->r3+
         r19->r6+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s19
    t =r11
    m = permission
    p = 1
    c = c9+c6
}
one sig rule1 extends Rule{}{
    s =s18
    t =r14
    m = prohibition
    p = 1
    c = c8+c7+c9+c2
}
one sig rule2 extends Rule{}{
    s =s4
    t =r15
    m = prohibition
    p = 3
    c = c3+c6+c4+c2+c0+c9
}
one sig rule3 extends Rule{}{
    s =s15
    t =r5
    m = permission
    p = 3
    c = c0+c9
}
one sig rule4 extends Rule{}{
    s =s17
    t =r4
    m = prohibition
    p = 4
    c = c2+c5+c0
}
one sig rule5 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 0
    c = c7+c5
}
one sig rule6 extends Rule{}{
    s =s16
    t =r2
    m = permission
    p = 3
    c = c1+c4+c3+c6+c2
}
one sig rule7 extends Rule{}{
    s =s1
    t =r2
    m = permission
    p = 4
    c = c7+c2+c0+c5+c8+c3
}
one sig rule8 extends Rule{}{
    s =s10
    t =r5
    m = permission
    p = 3
    c = c6+c3+c4
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
