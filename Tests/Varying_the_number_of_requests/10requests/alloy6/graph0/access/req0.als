module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s5->s3+
         s6->s0+
         s6->s1+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s4+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s7+
         s13->s10+
         s13->s12+
         s14->s2+
         s14->s4+
         s14->s9+
         s14->s11+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s11+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r4+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r5+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r8+
         r13->r0+
         r13->r1+
         r13->r5+
         r13->r6+
         r13->r8+
         r14->r3+
         r14->r5+
         r14->r9+
         r15->r0+
         r15->r2+
         r15->r6+
         r15->r8+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r2+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r5+
         r18->r10+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r2+
         r19->r6+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r16+
         r19->r18}

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
    s =s9
    t =r7
    m = permission
    p = 1
    c = c4+c3+c2+c8+c1+c7+c9
}
one sig rule1 extends Rule{}{
    s =s18
    t =r10
    m = prohibition
    p = 1
    c = c3+c1+c9+c5
}
one sig rule2 extends Rule{}{
    s =s3
    t =r1
    m = permission
    p = 0
    c = c7+c1+c9+c6+c3
}
one sig rule3 extends Rule{}{
    s =s15
    t =r4
    m = permission
    p = 1
    c = c6+c8+c9+c1+c5+c0
}
one sig rule4 extends Rule{}{
    s =s4
    t =r8
    m = prohibition
    p = 3
    c = c6+c2+c9+c7+c0+c8+c5
}
one sig rule5 extends Rule{}{
    s =s18
    t =r17
    m = prohibition
    p = 4
    c = c8+c4+c1+c3+c2
}
one sig rule6 extends Rule{}{
    s =s12
    t =r2
    m = prohibition
    p = 1
    c = c7+c0+c9+c3+c8
}
one sig rule7 extends Rule{}{
    s =s1
    t =r2
    m = permission
    p = 3
    c = c6+c0+c9+c2+c1+c4
}
one sig rule8 extends Rule{}{
    s =s11
    t =r18
    m = permission
    p = 3
    c = c2+c7+c0+c1+c4
}
one sig rule9 extends Rule{}{
    s =s13
    t =r4
    m = prohibition
    p = 4
    c = c9+c5+c3+c6+c8+c7
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
