module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s9+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s4+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s10+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s6+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s11+
         s17->s15+
         s18->s0+
         s18->s5+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s16+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r2+
         r7->r3+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r6+
         r11->r9+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r11+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r0+
         r19->r1+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r14+
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
    s =s3
    t =r3
    m = permission
    p = 0
    c = c7+c0
}
one sig rule1 extends Rule{}{
    s =s6
    t =r17
    m = permission
    p = 0
    c = c5+c2+c0+c9+c4
}
one sig rule2 extends Rule{}{
    s =s18
    t =r10
    m = permission
    p = 1
    c = c8
}
one sig rule3 extends Rule{}{
    s =s6
    t =r13
    m = permission
    p = 4
    c = c1+c6+c0+c2+c3
}
one sig rule4 extends Rule{}{
    s =s11
    t =r12
    m = prohibition
    p = 4
    c = c4
}
one sig rule5 extends Rule{}{
    s =s13
    t =r3
    m = permission
    p = 2
    c = c6+c1+c7+c4+c5+c2
}
one sig rule6 extends Rule{}{
    s =s12
    t =r2
    m = prohibition
    p = 1
    c = c6+c5+c2+c9+c4
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
