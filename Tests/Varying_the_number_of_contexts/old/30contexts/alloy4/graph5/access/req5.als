module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s0+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s11+
         s16->s15+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s4+
         s18->s7+
         s18->s8+
         s18->s14+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s10+
         s19->s12+
         s19->s14+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s6+
         s20->s7+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s12+
         s21->s16+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s2+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s20+
         s22->s21+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s19+
         s23->s21+
         s24->s0+
         s24->s2+
         s24->s5+
         s24->s10+
         s24->s13+
         s24->s17+
         s24->s19+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s7+
         s25->s10+
         s25->s14+
         s25->s16+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s0+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s18+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s0+
         s27->s3+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s23+
         s27->s26+
         s28->s6+
         s28->s7+
         s28->s12+
         s28->s16+
         s28->s19+
         s28->s21+
         s28->s23+
         s28->s24+
         s29->s0+
         s29->s7+
         s29->s11+
         s29->s12+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s20+
         s29->s21+
         s29->s24+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r3+
         r6->r1+
         r6->r3+
         r6->r5+
         r7->r2+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r6+
         r14->r11+
         r14->r12+
         r15->r2+
         r15->r7+
         r15->r10+
         r15->r13+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r5+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r18+
         r20->r0+
         r20->r2+
         r20->r7+
         r20->r8+
         r20->r11+
         r20->r12+
         r20->r19+
         r21->r0+
         r21->r6+
         r21->r12+
         r21->r15+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r14+
         r22->r15+
         r22->r17+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r4+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r15+
         r23->r17+
         r23->r18+
         r23->r20+
         r23->r21+
         r24->r1+
         r24->r2+
         r24->r5+
         r24->r8+
         r24->r12+
         r24->r19+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r13+
         r25->r14+
         r25->r16+
         r25->r19+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r15+
         r26->r22+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r13+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r28->r0+
         r28->r2+
         r28->r3+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r10+
         r28->r12+
         r28->r14+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r23+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r2+
         r29->r4+
         r29->r9+
         r29->r19+
         r29->r20+
         r29->r22+
         r29->r25+
         r29->r26+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s1
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r26
    m = prohibition
    p = 4
    c = c5+c6
}
one sig rule1 extends Rule{}{
    s =s4
    t =r8
    m = prohibition
    p = 0
    c = c4+c5+c6+c1
}
one sig rule2 extends Rule{}{
    s =s28
    t =r18
    m = prohibition
    p = 2
    c = c2+c9+c7+c4+c8
}
one sig rule3 extends Rule{}{
    s =s24
    t =r13
    m = permission
    p = 0
    c = c1+c7+c2+c3+c9
}
one sig rule4 extends Rule{}{
    s =s2
    t =r18
    m = prohibition
    p = 2
    c = c5+c4+c0
}
one sig rule5 extends Rule{}{
    s =s4
    t =r29
    m = permission
    p = 2
    c = c2+c9+c3+c1+c6
}
one sig rule6 extends Rule{}{
    s =s17
    t =r19
    m = prohibition
    p = 4
    c = c1+c2+c3+c5+c4+c6
}
one sig rule7 extends Rule{}{
    s =s20
    t =r7
    m = permission
    p = 2
    c = c5+c6+c8
}
one sig rule8 extends Rule{}{
    s =s25
    t =r21
    m = prohibition
    p = 1
    c = c6+c5+c2+c0+c8+c1+c4
}
one sig rule9 extends Rule{}{
    s =s28
    t =r18
    m = permission
    p = 2
    c = c0+c5+c9
}
one sig rule10 extends Rule{}{
    s =s4
    t =r20
    m = prohibition
    p = 4
    c = c2+c8+c0+c3
}
one sig rule11 extends Rule{}{
    s =s15
    t =r27
    m = permission
    p = 1
    c = c6+c1+c4+c7
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
run accessReq5_c0{access_condition[req5,c0]} for 4
run accessReq5_c1{access_condition[req5,c1]} for 4
run accessReq5_c2{access_condition[req5,c2]} for 4
run accessReq5_c3{access_condition[req5,c3]} for 4
run accessReq5_c4{access_condition[req5,c4]} for 4
run accessReq5_c5{access_condition[req5,c5]} for 4
run accessReq5_c6{access_condition[req5,c6]} for 4
run accessReq5_c7{access_condition[req5,c7]} for 4
run accessReq5_c8{access_condition[req5,c8]} for 4
run accessReq5_c9{access_condition[req5,c9]} for 4
