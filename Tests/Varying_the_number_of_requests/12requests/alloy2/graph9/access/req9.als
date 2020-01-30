module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s5->s0+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s7+
         s17->s11+
         s17->s12+
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
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r4+
         r6->r0+
         r6->r2+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r4+
         r9->r6+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r8+
         r13->r11+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r4+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r10+
         r16->r12+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r5+
         r19->r9+
         r19->r11+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req9 extends Request{}{
sub=s4
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r0
    m = prohibition
    p = 4
    c = c1+c9+c4
}
one sig rule1 extends Rule{}{
    s =s14
    t =r1
    m = permission
    p = 1
    c = c0+c5+c4+c7+c9
}
one sig rule2 extends Rule{}{
    s =s6
    t =r17
    m = prohibition
    p = 0
    c = c9+c3+c4+c6+c7
}
one sig rule3 extends Rule{}{
    s =s7
    t =r4
    m = prohibition
    p = 4
    c = c9+c6
}
one sig rule4 extends Rule{}{
    s =s3
    t =r7
    m = prohibition
    p = 4
    c = c8
}
one sig rule5 extends Rule{}{
    s =s2
    t =r12
    m = prohibition
    p = 4
    c = c9+c0+c4+c6+c7
}
one sig rule6 extends Rule{}{
    s =s13
    t =r1
    m = prohibition
    p = 0
    c = c8+c6+c9+c7+c2+c0+c5
}
one sig rule7 extends Rule{}{
    s =s3
    t =r4
    m = prohibition
    p = 2
    c = c8+c6+c1+c0+c2+c3+c5
}
one sig rule8 extends Rule{}{
    s =s13
    t =r13
    m = prohibition
    p = 1
    c = c8+c0+c6+c2+c4+c1
}
one sig rule9 extends Rule{}{
    s =s5
    t =r19
    m = permission
    p = 1
    c = c1+c6+c8
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
run accessReq9_c0{access_condition[req9,c0]} for 4
run accessReq9_c1{access_condition[req9,c1]} for 4
run accessReq9_c2{access_condition[req9,c2]} for 4
run accessReq9_c3{access_condition[req9,c3]} for 4
run accessReq9_c4{access_condition[req9,c4]} for 4
run accessReq9_c5{access_condition[req9,c5]} for 4
run accessReq9_c6{access_condition[req9,c6]} for 4
run accessReq9_c7{access_condition[req9,c7]} for 4
run accessReq9_c8{access_condition[req9,c8]} for 4
run accessReq9_c9{access_condition[req9,c9]} for 4
