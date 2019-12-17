module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
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
         s4->s0+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s7+
         s10->s2+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s7+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s12+
         s15->s4+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s10+
         s17->s0+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r8+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r2+
         r11->r4+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r5+
         r14->r8+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r3+
         r19->r7+
         r19->r10+
         r19->r12+
         r19->r15+
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
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 4
    c = c0+c3+c6+c8+c9+c4+c1+c5
}
one sig rule1 extends Rule{}{
    s =s2
    t =r6
    m = permission
    p = 4
    c = c4
}
one sig rule2 extends Rule{}{
    s =s1
    t =r9
    m = prohibition
    p = 3
    c = c1+c9+c7
}
one sig rule3 extends Rule{}{
    s =s8
    t =r9
    m = permission
    p = 0
    c = c5+c4+c9+c3
}
one sig rule4 extends Rule{}{
    s =s6
    t =r7
    m = permission
    p = 2
    c = c7+c3+c8+c0+c4
}
one sig rule5 extends Rule{}{
    s =s6
    t =r16
    m = prohibition
    p = 2
    c = c9+c8+c7+c1+c3+c4
}
one sig rule6 extends Rule{}{
    s =s2
    t =r9
    m = permission
    p = 1
    c = c1+c3+c7+c0+c4
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
