module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s5->s1+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s2+
         s8->s2+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s13->s0+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s13+
         s15->s2+
         s15->s8+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s3+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s15+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r0+
         r6->r1+
         r6->r3+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r8+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req11 extends Request{}{
sub=s4
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s9
    t =r8
    m = prohibition
    p = 2
    c = c2+c7+c4
}
one sig rule1 extends Rule{}{
    s =s16
    t =r14
    m = prohibition
    p = 1
    c = c1+c4+c8+c6+c0+c3
}
one sig rule2 extends Rule{}{
    s =s2
    t =r0
    m = prohibition
    p = 0
    c = c7+c8+c4+c1+c6+c2+c3
}
one sig rule3 extends Rule{}{
    s =s17
    t =r12
    m = prohibition
    p = 2
    c = c8
}
one sig rule4 extends Rule{}{
    s =s19
    t =r10
    m = prohibition
    p = 3
    c = c1+c2+c0+c8+c6+c3
}
one sig rule5 extends Rule{}{
    s =s0
    t =r13
    m = prohibition
    p = 0
    c = c9+c8+c3
}
one sig rule6 extends Rule{}{
    s =s7
    t =r0
    m = permission
    p = 3
    c = c1+c0+c4+c9+c7+c2+c6
}
one sig rule7 extends Rule{}{
    s =s0
    t =r12
    m = permission
    p = 0
    c = c6+c2+c7+c0+c5+c1+c3
}
one sig rule8 extends Rule{}{
    s =s1
    t =r17
    m = permission
    p = 2
    c = c3+c4
}
one sig rule9 extends Rule{}{
    s =s15
    t =r12
    m = permission
    p = 0
    c = c4
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
run accessReq11_c0{access_condition[req11,c0]} for 4
run accessReq11_c1{access_condition[req11,c1]} for 4
run accessReq11_c2{access_condition[req11,c2]} for 4
run accessReq11_c3{access_condition[req11,c3]} for 4
run accessReq11_c4{access_condition[req11,c4]} for 4
run accessReq11_c5{access_condition[req11,c5]} for 4
run accessReq11_c6{access_condition[req11,c6]} for 4
run accessReq11_c7{access_condition[req11,c7]} for 4
run accessReq11_c8{access_condition[req11,c8]} for 4
run accessReq11_c9{access_condition[req11,c9]} for 4
