module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s2+
         s4->s0+
         s4->s2+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s3+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s3+
         s11->s5+
         s11->s7+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s7+
         s14->s10+
         s15->s0+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s14+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s11+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r9+
         r11->r2+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r2+
         r12->r6+
         r12->r7+
         r12->r8+
         r13->r0+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r14+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r9
    m = permission
    p = 4
    c = c0+c9
}
one sig rule1 extends Rule{}{
    s =s11
    t =r13
    m = permission
    p = 4
    c = c9+c2+c4+c6+c8+c5
}
one sig rule2 extends Rule{}{
    s =s7
    t =r15
    m = prohibition
    p = 3
    c = c1+c9+c4+c5+c7+c3
}
one sig rule3 extends Rule{}{
    s =s3
    t =r4
    m = prohibition
    p = 3
    c = c6
}
one sig rule4 extends Rule{}{
    s =s5
    t =r6
    m = permission
    p = 3
    c = c6+c2+c9+c8
}
one sig rule5 extends Rule{}{
    s =s5
    t =r7
    m = permission
    p = 1
    c = c0+c9+c6+c1+c2+c8
}
one sig rule6 extends Rule{}{
    s =s3
    t =r8
    m = prohibition
    p = 1
    c = c8+c2+c5+c1+c3+c6+c9
}
one sig rule7 extends Rule{}{
    s =s8
    t =r1
    m = prohibition
    p = 0
    c = c3+c2+c7+c0
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
run accessReq0_c0{access_condition[req0,c0]} for 4
run accessReq0_c1{access_condition[req0,c1]} for 4
run accessReq0_c2{access_condition[req0,c2]} for 4
run accessReq0_c3{access_condition[req0,c3]} for 4
run accessReq0_c4{access_condition[req0,c4]} for 4
run accessReq0_c5{access_condition[req0,c5]} for 4
run accessReq0_c6{access_condition[req0,c6]} for 4
run accessReq0_c7{access_condition[req0,c7]} for 4
run accessReq0_c8{access_condition[req0,c8]} for 4
run accessReq0_c9{access_condition[req0,c9]} for 4
