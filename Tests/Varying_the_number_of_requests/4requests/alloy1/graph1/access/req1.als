module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s2+
         s6->s1+
         s6->s2+
         s6->s3+
         s7->s1+
         s7->s2+
         s7->s5+
         s8->s0+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s7+
         s14->s8+
         s14->s11+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s12+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s12+
         s17->s13+
         s18->s0+
         s18->s1+
         s18->s7+
         s18->s8+
         s18->s12+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r4+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r1+
         r12->r3+
         r12->r9+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r9+
         r13->r12+
         r14->r1+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r15->r0+
         r15->r4+
         r15->r8+
         r15->r9+
         r15->r10+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r4+
         r19->r6+
         r19->r11+
         r19->r13+
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
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r9
    m = permission
    p = 1
    c = c8+c1+c0+c4
}
one sig rule1 extends Rule{}{
    s =s9
    t =r18
    m = prohibition
    p = 0
    c = c2+c1+c7+c3
}
one sig rule2 extends Rule{}{
    s =s5
    t =r2
    m = prohibition
    p = 1
    c = c1
}
one sig rule3 extends Rule{}{
    s =s18
    t =r3
    m = prohibition
    p = 4
    c = c7+c0+c3+c6+c8+c4+c2+c9
}
one sig rule4 extends Rule{}{
    s =s12
    t =r18
    m = permission
    p = 0
    c = c8+c9+c5+c6
}
one sig rule5 extends Rule{}{
    s =s7
    t =r11
    m = prohibition
    p = 2
    c = c7+c4+c0+c5+c3+c8
}
one sig rule6 extends Rule{}{
    s =s9
    t =r16
    m = permission
    p = 3
    c = c1+c6+c4
}
one sig rule7 extends Rule{}{
    s =s7
    t =r18
    m = prohibition
    p = 3
    c = c7+c2+c6+c8+c1+c0
}
one sig rule8 extends Rule{}{
    s =s14
    t =r9
    m = permission
    p = 3
    c = c5+c1
}
one sig rule9 extends Rule{}{
    s =s19
    t =r10
    m = prohibition
    p = 0
    c = c7+c5+c3
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
