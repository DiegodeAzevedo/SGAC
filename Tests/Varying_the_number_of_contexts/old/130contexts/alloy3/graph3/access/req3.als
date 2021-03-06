module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s4+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s5+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s7+
         s12->s8+
         s12->s9+
         s13->s0+
         s13->s2+
         s13->s5+
         s13->s8+
         s13->s11+
         s14->s0+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s15->s1+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s12+
         s16->s0+
         s16->s2+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s12+
         s17->s13+
         s18->s2+
         s18->s4+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s14+
         s19->s17+
         s20->s2+
         s20->s4+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s17+
         s21->s0+
         s21->s1+
         s21->s5+
         s21->s7+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s17+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s8+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s18+
         s22->s19+
         s22->s20+
         s23->s4+
         s23->s6+
         s23->s9+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s15+
         s23->s16+
         s23->s19+
         s23->s22+
         s24->s1+
         s24->s4+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s14+
         s24->s16+
         s24->s18+
         s24->s19+
         s25->s3+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s16+
         s26->s19+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s7+
         s27->s8+
         s27->s10+
         s27->s12+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s19+
         s28->s22+
         s28->s23+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s7+
         s29->s8+
         s29->s14+
         s29->s18+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r3+
         r10->r4+
         r10->r7+
         r11->r1+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r10+
         r13->r1+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r8+
         r14->r9+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r14+
         r18->r17+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r10+
         r20->r12+
         r20->r16+
         r20->r18+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r8+
         r21->r12+
         r21->r16+
         r21->r18+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r16+
         r22->r21+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r8+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r22+
         r24->r1+
         r24->r7+
         r24->r9+
         r24->r14+
         r24->r16+
         r24->r18+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r5+
         r25->r6+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r15+
         r26->r18+
         r26->r19+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r4+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r20+
         r27->r22+
         r27->r23+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r8+
         r28->r10+
         r28->r11+
         r28->r14+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r12+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r21+
         r29->r26}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s9
    t =r2
    m = permission
    p = 1
    c = c8
}
one sig rule1 extends Rule{}{
    s =s1
    t =r21
    m = prohibition
    p = 3
    c = c7+c8+c2+c5
}
one sig rule2 extends Rule{}{
    s =s2
    t =r9
    m = prohibition
    p = 4
    c = c2+c5
}
one sig rule3 extends Rule{}{
    s =s21
    t =r15
    m = permission
    p = 4
    c = c4+c8+c9
}
one sig rule4 extends Rule{}{
    s =s26
    t =r17
    m = prohibition
    p = 0
    c = c7+c2+c4+c9
}
one sig rule5 extends Rule{}{
    s =s6
    t =r14
    m = permission
    p = 0
    c = c4+c6+c3+c5+c1+c8+c0
}
one sig rule6 extends Rule{}{
    s =s18
    t =r29
    m = permission
    p = 2
    c = c3+c6+c8+c9+c4
}
one sig rule7 extends Rule{}{
    s =s26
    t =r6
    m = permission
    p = 2
    c = c7+c6+c1+c3
}
one sig rule8 extends Rule{}{
    s =s22
    t =r25
    m = permission
    p = 4
    c = c7+c5+c8+c4
}
one sig rule9 extends Rule{}{
    s =s23
    t =r22
    m = prohibition
    p = 0
    c = c8+c9+c0
}
one sig rule10 extends Rule{}{
    s =s0
    t =r29
    m = permission
    p = 4
    c = c8+c1+c0+c3+c7+c9+c6
}
one sig rule11 extends Rule{}{
    s =s13
    t =r28
    m = permission
    p = 1
    c = c3
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
run accessReq3_c0{access_condition[req3,c0]} for 4
run accessReq3_c1{access_condition[req3,c1]} for 4
run accessReq3_c2{access_condition[req3,c2]} for 4
run accessReq3_c3{access_condition[req3,c3]} for 4
run accessReq3_c4{access_condition[req3,c4]} for 4
run accessReq3_c5{access_condition[req3,c5]} for 4
run accessReq3_c6{access_condition[req3,c6]} for 4
run accessReq3_c7{access_condition[req3,c7]} for 4
run accessReq3_c8{access_condition[req3,c8]} for 4
run accessReq3_c9{access_condition[req3,c9]} for 4
