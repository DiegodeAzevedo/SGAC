module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s1+
         s5->s0+
         s6->s0+
         s6->s2+
         s6->s4+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s6+
         s10->s8+
         s11->s1+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s8+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s11+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s7+
         s15->s8+
         s15->s13+
         s16->s2+
         s16->s6+
         s16->s8+
         s16->s11+
         s17->s1+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s6+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s12+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s3+
         s23->s5+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s13+
         s23->s15+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s10+
         s24->s13+
         s24->s14+
         s24->s16+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s22+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s6+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s16+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s4+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s11+
         s26->s13+
         s26->s16+
         s26->s21+
         s26->s23+
         s26->s25+
         s27->s1+
         s27->s3+
         s27->s7+
         s27->s12+
         s27->s13+
         s27->s19+
         s27->s21+
         s27->s23+
         s27->s26+
         s28->s2+
         s28->s4+
         s28->s10+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s7+
         s29->s10+
         s29->s15+
         s29->s17+
         s29->s21+
         s29->s23+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r2+
         r7->r4+
         r8->r2+
         r8->r3+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r5+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r8+
         r12->r1+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r7+
         r13->r10+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r11+
         r15->r2+
         r15->r5+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r10+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r7+
         r18->r10+
         r18->r14+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r5+
         r19->r11+
         r19->r13+
         r19->r15+
         r19->r16+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r8+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r16+
         r20->r19+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r16+
         r21->r17+
         r21->r18+
         r22->r0+
         r22->r1+
         r22->r4+
         r22->r7+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r18+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r19+
         r25->r0+
         r25->r1+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r15+
         r25->r18+
         r25->r22+
         r26->r0+
         r26->r4+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r16+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r11+
         r27->r16+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r23+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r2+
         r28->r3+
         r28->r5+
         r28->r10+
         r28->r11+
         r28->r15+
         r28->r18+
         r28->r19+
         r28->r22+
         r28->r24+
         r29->r0+
         r29->r1+
         r29->r4+
         r29->r6+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r21+
         r29->r25+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s2
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s19
    t =r22
    m = prohibition
    p = 4
    c = c6
}
one sig rule1 extends Rule{}{
    s =s9
    t =r29
    m = prohibition
    p = 3
    c = c5+c0+c8+c9+c7+c2
}
one sig rule2 extends Rule{}{
    s =s22
    t =r0
    m = permission
    p = 4
    c = c5+c0
}
one sig rule3 extends Rule{}{
    s =s2
    t =r25
    m = prohibition
    p = 4
    c = c7+c3+c6+c0+c4+c1
}
one sig rule4 extends Rule{}{
    s =s27
    t =r16
    m = prohibition
    p = 2
    c = c3+c1+c8+c0+c5+c2+c4
}
one sig rule5 extends Rule{}{
    s =s10
    t =r12
    m = permission
    p = 0
    c = c1+c6
}
one sig rule6 extends Rule{}{
    s =s6
    t =r19
    m = permission
    p = 4
    c = c1+c3+c7
}
one sig rule7 extends Rule{}{
    s =s1
    t =r7
    m = permission
    p = 1
    c = c7+c2+c5+c3
}
one sig rule8 extends Rule{}{
    s =s15
    t =r23
    m = prohibition
    p = 2
    c = c7+c9+c4+c8+c6
}
one sig rule9 extends Rule{}{
    s =s3
    t =r0
    m = prohibition
    p = 3
    c = c1+c3+c4
}
one sig rule10 extends Rule{}{
    s =s10
    t =r23
    m = prohibition
    p = 4
    c = c8+c2
}
one sig rule11 extends Rule{}{
    s =s11
    t =r0
    m = prohibition
    p = 3
    c = c0+c1+c3+c2+c6+c7+c8
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
