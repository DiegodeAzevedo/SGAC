module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s3+
         s6->s0+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s3+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s1+
         s14->s5+
         s14->s6+
         s14->s8+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s7+
         s15->s9+
         s15->s11+
         s15->s14+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s9+
         s16->s11+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s6+
         s17->s8+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s14+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s17+
         s20->s2+
         s20->s6+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s2+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s15+
         s22->s19+
         s22->s21+
         s23->s0+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s11+
         s23->s12+
         s23->s20+
         s24->s0+
         s24->s2+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s15+
         s24->s16+
         s24->s18+
         s24->s20+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s9+
         s25->s10+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s14+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s25+
         s27->s3+
         s27->s5+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s1+
         s28->s4+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s14+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s21+
         s28->s23+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s3+
         s29->s5+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r1+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r7+
         r10->r9+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r12->r2+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r10+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r8+
         r14->r0+
         r14->r2+
         r14->r5+
         r14->r7+
         r14->r11+
         r14->r12+
         r15->r3+
         r15->r6+
         r15->r9+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r8+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r12+
         r19->r13+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r11+
         r20->r14+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r14+
         r21->r17+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r6+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r20+
         r23->r2+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r16+
         r23->r18+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r2+
         r25->r4+
         r25->r6+
         r25->r8+
         r25->r9+
         r25->r12+
         r25->r14+
         r25->r18+
         r25->r20+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r24+
         r27->r1+
         r27->r4+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r11+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r8+
         r28->r10+
         r28->r12+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r20+
         r29->r23+
         r29->r24+
         r29->r25+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r8
    m = prohibition
    p = 2
    c = c1+c2+c4+c5+c8
}
one sig rule1 extends Rule{}{
    s =s27
    t =r13
    m = permission
    p = 4
    c = c3+c2+c5
}
one sig rule2 extends Rule{}{
    s =s19
    t =r18
    m = prohibition
    p = 2
    c = c0+c8+c1
}
one sig rule3 extends Rule{}{
    s =s13
    t =r17
    m = permission
    p = 0
    c = c1+c6+c0
}
one sig rule4 extends Rule{}{
    s =s7
    t =r20
    m = permission
    p = 2
    c = c6+c4
}
one sig rule5 extends Rule{}{
    s =s23
    t =r17
    m = prohibition
    p = 0
    c = c4+c3+c2+c0+c1+c9+c7
}
one sig rule6 extends Rule{}{
    s =s29
    t =r20
    m = prohibition
    p = 1
    c = c4+c5+c6+c7+c1
}
one sig rule7 extends Rule{}{
    s =s13
    t =r20
    m = prohibition
    p = 1
    c = c6+c7+c2+c8+c4+c3+c9
}
one sig rule8 extends Rule{}{
    s =s10
    t =r17
    m = prohibition
    p = 4
    c = c3+c1+c5
}
one sig rule9 extends Rule{}{
    s =s9
    t =r16
    m = permission
    p = 1
    c = c0+c9
}
one sig rule10 extends Rule{}{
    s =s7
    t =r24
    m = prohibition
    p = 1
    c = c1+c5+c8+c7+c0+c6
}
one sig rule11 extends Rule{}{
    s =s11
    t =r3
    m = permission
    p = 3
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
run accessReq2_c0{access_condition[req2,c0]} for 4
run accessReq2_c1{access_condition[req2,c1]} for 4
run accessReq2_c2{access_condition[req2,c2]} for 4
run accessReq2_c3{access_condition[req2,c3]} for 4
run accessReq2_c4{access_condition[req2,c4]} for 4
run accessReq2_c5{access_condition[req2,c5]} for 4
run accessReq2_c6{access_condition[req2,c6]} for 4
run accessReq2_c7{access_condition[req2,c7]} for 4
run accessReq2_c8{access_condition[req2,c8]} for 4
run accessReq2_c9{access_condition[req2,c9]} for 4
