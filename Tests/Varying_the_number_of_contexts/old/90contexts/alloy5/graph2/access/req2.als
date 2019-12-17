module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s2+
         s4->s0+
         s5->s2+
         s5->s3+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s8+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s10+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s13+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s14+
         s18->s1+
         s18->s5+
         s18->s8+
         s18->s11+
         s19->s0+
         s19->s3+
         s19->s4+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s12+
         s20->s0+
         s20->s3+
         s20->s6+
         s20->s9+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s19+
         s21->s0+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s11+
         s21->s15+
         s21->s18+
         s21->s20+
         s22->s1+
         s22->s4+
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
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s7+
         s23->s11+
         s23->s12+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s5+
         s24->s7+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s21+
         s24->s22+
         s25->s2+
         s25->s7+
         s25->s10+
         s25->s12+
         s25->s14+
         s25->s17+
         s25->s18+
         s25->s20+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s18+
         s26->s20+
         s26->s22+
         s26->s23+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s8+
         s27->s13+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s21+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s4+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s24+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s6+
         s29->s8+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s24}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r6+
         r9->r8+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r4+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r4+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r14+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r13+
         r17->r1+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r10+
         r18->r11+
         r18->r15+
         r19->r1+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r13+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r10+
         r21->r15+
         r22->r1+
         r22->r5+
         r22->r6+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r22+
         r24->r0+
         r24->r3+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r16+
         r24->r18+
         r25->r1+
         r25->r3+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r22+
         r25->r23+
         r26->r1+
         r26->r2+
         r26->r4+
         r26->r7+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r20+
         r26->r21+
         r26->r23+
         r26->r25+
         r27->r15+
         r27->r19+
         r27->r22+
         r27->r26+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r15+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r23+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r3+
         r29->r4+
         r29->r11+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r22+
         r29->r23+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s6
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r21
    m = prohibition
    p = 4
    c = c9
}
one sig rule1 extends Rule{}{
    s =s7
    t =r16
    m = permission
    p = 1
    c = c5+c3+c2+c8+c6+c7
}
one sig rule2 extends Rule{}{
    s =s11
    t =r26
    m = prohibition
    p = 1
    c = c1+c7+c4+c8+c2+c0
}
one sig rule3 extends Rule{}{
    s =s27
    t =r21
    m = permission
    p = 0
    c = c8+c3+c1
}
one sig rule4 extends Rule{}{
    s =s6
    t =r4
    m = permission
    p = 3
    c = c7+c2+c8+c1+c5
}
one sig rule5 extends Rule{}{
    s =s27
    t =r23
    m = prohibition
    p = 3
    c = c4+c9+c0+c3+c7+c5+c8
}
one sig rule6 extends Rule{}{
    s =s3
    t =r20
    m = prohibition
    p = 1
    c = c7+c8+c3+c0
}
one sig rule7 extends Rule{}{
    s =s12
    t =r1
    m = permission
    p = 3
    c = c3
}
one sig rule8 extends Rule{}{
    s =s12
    t =r3
    m = prohibition
    p = 4
    c = c7+c1+c4
}
one sig rule9 extends Rule{}{
    s =s10
    t =r27
    m = permission
    p = 3
    c = c7+c6+c4
}
one sig rule10 extends Rule{}{
    s =s28
    t =r3
    m = prohibition
    p = 4
    c = c7+c0+c3+c4
}
one sig rule11 extends Rule{}{
    s =s26
    t =r6
    m = prohibition
    p = 1
    c = c5+c8+c0+c9
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
