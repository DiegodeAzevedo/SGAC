module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s4+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s9+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s17->s6+
         s17->s11+
         s17->s12+
         s18->s2+
         s18->s5+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s12+
         s19->s14+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r3+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r8+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r5+
         r14->r7+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r11+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r16}

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
    s =s3
    t =r19
    m = permission
    p = 0
    c = c0+c4+c7+c8+c2+c9
}
one sig rule1 extends Rule{}{
    s =s7
    t =r19
    m = prohibition
    p = 2
    c = c1+c8+c4+c5+c0+c3
}
one sig rule2 extends Rule{}{
    s =s18
    t =r5
    m = prohibition
    p = 2
    c = c3+c2+c7+c4+c6+c0+c8
}
one sig rule3 extends Rule{}{
    s =s10
    t =r4
    m = prohibition
    p = 2
    c = c5+c7+c2+c0+c1+c3+c6
}
one sig rule4 extends Rule{}{
    s =s19
    t =r5
    m = prohibition
    p = 2
    c = c3+c2+c6
}
one sig rule5 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 0
    c = c2+c8+c7+c4+c1+c0+c3
}
one sig rule6 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 3
    c = c1
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
