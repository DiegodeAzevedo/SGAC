module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s5+
         s14->s10+
         s14->s13+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s11+
         s15->s13+
         s16->s2+
         s16->s5+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s5+
         s18->s6+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r2+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r5+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r6+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r12+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r14+
         r18->r17+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r15}

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
    s =s4
    t =r2
    m = permission
    p = 1
    c = c9+c7+c1+c6+c4
}
one sig rule1 extends Rule{}{
    s =s1
    t =r9
    m = prohibition
    p = 0
    c = c0+c9+c7+c5
}
one sig rule2 extends Rule{}{
    s =s10
    t =r7
    m = prohibition
    p = 2
    c = c0+c3+c8+c2+c7
}
one sig rule3 extends Rule{}{
    s =s3
    t =r8
    m = permission
    p = 3
    c = c4+c5+c8+c7+c1
}
one sig rule4 extends Rule{}{
    s =s2
    t =r10
    m = permission
    p = 3
    c = c4+c3+c6+c8+c0+c2+c1
}
one sig rule5 extends Rule{}{
    s =s13
    t =r4
    m = permission
    p = 2
    c = c4+c3+c9+c7+c8
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
