module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s6->s2+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s1+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s5+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s12+
         s17->s0+
         s17->s2+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r4->r0+
         r4->r2+
         r5->r1+
         r5->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r7+
         r10->r0+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r1+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r6+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r10+
         r16->r12+
         r17->r1+
         r17->r2+
         r17->r6+
         r17->r8+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r4+
         r18->r6+
         r18->r8+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r4+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r15+
         r19->r16+
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
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r17
    m = prohibition
    p = 0
    c = c5+c3+c4+c9+c6+c7+c8+c0
}
one sig rule1 extends Rule{}{
    s =s7
    t =r12
    m = permission
    p = 4
    c = c9
}
one sig rule2 extends Rule{}{
    s =s13
    t =r6
    m = prohibition
    p = 4
    c = c2+c7+c0+c9+c3+c6
}
one sig rule3 extends Rule{}{
    s =s8
    t =r5
    m = permission
    p = 1
    c = c6+c5+c1+c4
}
one sig rule4 extends Rule{}{
    s =s10
    t =r1
    m = permission
    p = 4
    c = c2
}
one sig rule5 extends Rule{}{
    s =s4
    t =r10
    m = permission
    p = 3
    c = c3+c1+c0+c6
}
one sig rule6 extends Rule{}{
    s =s15
    t =r16
    m = permission
    p = 0
    c = c7+c6+c8
}
one sig rule7 extends Rule{}{
    s =s7
    t =r10
    m = permission
    p = 4
    c = c2+c5+c4+c7
}
one sig rule8 extends Rule{}{
    s =s16
    t =r2
    m = prohibition
    p = 1
    c = c9+c0+c7+c4+c5
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
