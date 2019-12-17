module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s8+
         s11->s0+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s4+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s18->s0+
         s18->s2+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r4+
         r7->r0+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r6+
         r9->r2+
         r9->r3+
         r9->r8+
         r10->r3+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r5+
         r12->r6+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r5+
         r13->r9+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r7+
         r15->r10+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r9+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r18->r0+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r15}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s1
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r14
    m = permission
    p = 2
    c = c7+c0+c2+c3
}
one sig rule1 extends Rule{}{
    s =s18
    t =r19
    m = prohibition
    p = 1
    c = c6+c9+c8
}
one sig rule2 extends Rule{}{
    s =s1
    t =r8
    m = prohibition
    p = 4
    c = c5
}
one sig rule3 extends Rule{}{
    s =s3
    t =r2
    m = permission
    p = 2
    c = c0+c1+c7+c9+c4
}
one sig rule4 extends Rule{}{
    s =s9
    t =r14
    m = permission
    p = 3
    c = c9+c4+c8+c1+c3+c6+c5
}
one sig rule5 extends Rule{}{
    s =s13
    t =r8
    m = prohibition
    p = 0
    c = c3+c8+c0+c4+c6+c2+c9
}
one sig rule6 extends Rule{}{
    s =s0
    t =r10
    m = prohibition
    p = 1
    c = c9+c4+c0+c5
}
one sig rule7 extends Rule{}{
    s =s3
    t =r0
    m = permission
    p = 2
    c = c9+c6+c4
}
one sig rule8 extends Rule{}{
    s =s0
    t =r14
    m = prohibition
    p = 4
    c = c1+c2+c3+c9
}
one sig rule9 extends Rule{}{
    s =s12
    t =r18
    m = permission
    p = 2
    c = c7+c5+c9+c4+c6
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
run accessReq4_c0{access_condition[req4,c0]} for 4
run accessReq4_c1{access_condition[req4,c1]} for 4
run accessReq4_c2{access_condition[req4,c2]} for 4
run accessReq4_c3{access_condition[req4,c3]} for 4
run accessReq4_c4{access_condition[req4,c4]} for 4
run accessReq4_c5{access_condition[req4,c5]} for 4
run accessReq4_c6{access_condition[req4,c6]} for 4
run accessReq4_c7{access_condition[req4,c7]} for 4
run accessReq4_c8{access_condition[req4,c8]} for 4
run accessReq4_c9{access_condition[req4,c9]} for 4
