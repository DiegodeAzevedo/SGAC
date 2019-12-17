module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s1+
         s4->s3+
         s5->s1+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s6+
         s10->s1+
         s10->s3+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s7+
         s11->s10+
         s12->s2+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s6+
         s18->s11+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s9+
         s20->s10+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s3+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s13+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s14+
         s22->s17+
         s22->s19+
         s22->s20+
         s22->s21}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r6+
         r8->r7+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r4+
         r12->r6+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r13+
         r15->r3+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r2+
         r16->r5+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r7+
         r17->r8+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r11+
         r18->r14+
         r18->r15+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r15+
         r19->r18+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r15+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r9+
         r21->r11+
         r21->r16+
         r21->r18+
         r21->r19}

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
    s =s6
    t =r16
    m = permission
    p = 3
    c = c8+c9+c1
}
one sig rule1 extends Rule{}{
    s =s19
    t =r15
    m = prohibition
    p = 0
    c = c5+c4+c7
}
one sig rule2 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 1
    c = c7+c8+c1+c0+c4+c5+c2
}
one sig rule3 extends Rule{}{
    s =s18
    t =r2
    m = prohibition
    p = 1
    c = c9+c3+c8+c6+c0+c7
}
one sig rule4 extends Rule{}{
    s =s7
    t =r9
    m = permission
    p = 4
    c = c4+c9+c8+c7+c1+c5
}
one sig rule5 extends Rule{}{
    s =s16
    t =r10
    m = prohibition
    p = 1
    c = c1+c0+c2+c7+c9+c4+c6
}
one sig rule6 extends Rule{}{
    s =s18
    t =r21
    m = permission
    p = 2
    c = c7+c2
}
one sig rule7 extends Rule{}{
    s =s2
    t =r8
    m = permission
    p = 4
    c = c6+c8
}
one sig rule8 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 3
    c = c3+c1
}
one sig rule9 extends Rule{}{
    s =s19
    t =r2
    m = permission
    p = 2
    c = c6+c7
}
one sig rule10 extends Rule{}{
    s =s6
    t =r11
    m = permission
    p = 2
    c = c6+c3+c5+c7+c2+c8
}
one sig rule11 extends Rule{}{
    s =s18
    t =r4
    m = prohibition
    p = 2
    c = c7+c3+c1+c4+c8+c6
}
one sig rule12 extends Rule{}{
    s =s14
    t =r17
    m = permission
    p = 0
    c = c7+c0+c9+c5
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
