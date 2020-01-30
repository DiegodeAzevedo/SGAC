module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s5->s1+
         s6->s4+
         s7->s1+
         s8->s1+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s4+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s4+
         s15->s8+
         s15->s12+
         s15->s14+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s14+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r4->r0+
         r4->r3+
         r5->r2+
         r6->r1+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r7+
         r9->r0+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r12->r2+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r5+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r10+
         r16->r0+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r3+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r4+
         r19->r5+
         r19->r6+
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
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r16
    m = permission
    p = 4
    c = c5+c4+c2+c7+c3+c8+c1
}
one sig rule1 extends Rule{}{
    s =s6
    t =r8
    m = permission
    p = 1
    c = c7+c5+c3+c6
}
one sig rule2 extends Rule{}{
    s =s1
    t =r12
    m = permission
    p = 4
    c = c3
}
one sig rule3 extends Rule{}{
    s =s19
    t =r14
    m = prohibition
    p = 4
    c = c9
}
one sig rule4 extends Rule{}{
    s =s5
    t =r14
    m = permission
    p = 1
    c = c1+c4+c8+c2+c5+c0
}
one sig rule5 extends Rule{}{
    s =s2
    t =r8
    m = permission
    p = 2
    c = c5+c6+c3
}
one sig rule6 extends Rule{}{
    s =s6
    t =r9
    m = permission
    p = 3
    c = c2
}
one sig rule7 extends Rule{}{
    s =s10
    t =r19
    m = prohibition
    p = 2
    c = c5+c7+c8+c0+c6+c9
}
one sig rule8 extends Rule{}{
    s =s13
    t =r2
    m = permission
    p = 1
    c = c5+c4+c1+c8+c7
}
one sig rule9 extends Rule{}{
    s =s3
    t =r2
    m = prohibition
    p = 3
    c = c3+c7
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
