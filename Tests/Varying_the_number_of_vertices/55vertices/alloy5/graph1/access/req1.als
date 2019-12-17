module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s5+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s7+
         s12->s10+
         s13->s1+
         s13->s4+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s12+
         s15->s13+
         s16->s1+
         s16->s3+
         s16->s9+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s16+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s12+
         s19->s14+
         s19->s17+
         s20->s1+
         s20->s3+
         s20->s5+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s15+
         s20->s18+
         s21->s0+
         s21->s5+
         s21->s7+
         s21->s10+
         s21->s14+
         s21->s16+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s6+
         s22->s11+
         s22->s14+
         s22->s17+
         s22->s20+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s10+
         s23->s13+
         s23->s14+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s9+
         s25->s10+
         s25->s13+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s7+
         s26->s8+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s2+
         s27->s4+
         s27->s6+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s16+
         s27->s17+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r3+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r2+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r6+
         r13->r8+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r2+
         r14->r5+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r5+
         r18->r8+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r15+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r6+
         r20->r8+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r16+
         r20->r18+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r14+
         r21->r15+
         r21->r19+
         r22->r0+
         r22->r4+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r18+
         r22->r19+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r17+
         r23->r20+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r14+
         r24->r15+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r7+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r23+
         r25->r24+
         r26->r3+
         r26->r4+
         r26->r8+
         r26->r9+
         r26->r12+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s12
    t =r8
    m = prohibition
    p = 0
    c = c2
}
one sig rule1 extends Rule{}{
    s =s6
    t =r1
    m = permission
    p = 1
    c = c3+c0+c7+c9+c6
}
one sig rule2 extends Rule{}{
    s =s12
    t =r18
    m = permission
    p = 3
    c = c0+c6+c3+c2
}
one sig rule3 extends Rule{}{
    s =s21
    t =r25
    m = prohibition
    p = 2
    c = c9+c5+c8+c3
}
one sig rule4 extends Rule{}{
    s =s15
    t =r14
    m = permission
    p = 1
    c = c3+c0+c1+c5+c6+c7+c4+c2
}
one sig rule5 extends Rule{}{
    s =s22
    t =r6
    m = permission
    p = 0
    c = c4+c8+c3+c1+c9+c0+c7
}
one sig rule6 extends Rule{}{
    s =s14
    t =r23
    m = permission
    p = 0
    c = c6+c9+c0+c2+c3
}
one sig rule7 extends Rule{}{
    s =s15
    t =r18
    m = permission
    p = 3
    c = c7+c4+c0
}
one sig rule8 extends Rule{}{
    s =s23
    t =r15
    m = prohibition
    p = 1
    c = c9+c3+c8+c6+c0+c1
}
one sig rule9 extends Rule{}{
    s =s26
    t =r18
    m = prohibition
    p = 1
    c = c7+c9
}
one sig rule10 extends Rule{}{
    s =s19
    t =r5
    m = permission
    p = 2
    c = c2+c0+c1+c8+c9
}
one sig rule11 extends Rule{}{
    s =s12
    t =r24
    m = permission
    p = 4
    c = c3+c5+c8+c7
}
one sig rule12 extends Rule{}{
    s =s23
    t =r8
    m = permission
    p = 1
    c = c0+c1+c4+c2+c8
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
