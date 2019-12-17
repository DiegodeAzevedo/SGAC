module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s5+
         s7->s1+
         s7->s5+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s10+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s15->s0+
         s15->s1+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s13+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s9+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s5+
         s20->s7+
         s20->s9+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s12+
         s21->s13+
         s21->s16+
         s21->s17+
         s21->s19+
         s21->s20+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s12+
         s22->s14+
         s22->s17+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s5+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s14+
         s23->s16+
         s23->s21+
         s23->s22+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s20+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s15+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s4+
         s26->s12+
         s26->s15+
         s26->s18+
         s26->s19+
         s26->s21+
         s26->s22+
         s26->s25+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s18+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s13+
         s28->s16+
         s28->s18+
         s28->s20+
         s28->s26+
         s28->s27+
         s29->s4+
         s29->s7+
         s29->s9+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r5->r0+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r5+
         r7->r2+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r4+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r11+
         r14->r5+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r12+
         r18->r14+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r16+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r13+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r20+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r17+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r19+
         r23->r20+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r13+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r23+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r14+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r21+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r21+
         r26->r25+
         r27->r1+
         r27->r3+
         r27->r5+
         r27->r6+
         r27->r8+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r22+
         r27->r24+
         r28->r0+
         r28->r2+
         r28->r3+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r22+
         r28->r25+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r8+
         r29->r9+
         r29->r11+
         r29->r15+
         r29->r16+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r23+
         r29->r24+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s24
    t =r1
    m = permission
    p = 2
    c = c0+c7+c6+c4+c1+c3+c9
}
one sig rule1 extends Rule{}{
    s =s4
    t =r10
    m = prohibition
    p = 3
    c = c9
}
one sig rule2 extends Rule{}{
    s =s15
    t =r7
    m = permission
    p = 1
    c = c6+c3+c1+c4
}
one sig rule3 extends Rule{}{
    s =s20
    t =r18
    m = prohibition
    p = 1
    c = c6+c1+c8+c0+c7+c3
}
one sig rule4 extends Rule{}{
    s =s17
    t =r16
    m = prohibition
    p = 4
    c = c5+c6+c2
}
one sig rule5 extends Rule{}{
    s =s0
    t =r2
    m = permission
    p = 0
    c = c5
}
one sig rule6 extends Rule{}{
    s =s14
    t =r15
    m = prohibition
    p = 2
    c = c8
}
one sig rule7 extends Rule{}{
    s =s6
    t =r29
    m = permission
    p = 1
    c = c6+c5
}
one sig rule8 extends Rule{}{
    s =s1
    t =r18
    m = prohibition
    p = 4
    c = c1+c3+c9+c8
}
one sig rule9 extends Rule{}{
    s =s3
    t =r11
    m = permission
    p = 4
    c = c6+c9+c2+c7+c8+c0
}
one sig rule10 extends Rule{}{
    s =s3
    t =r12
    m = permission
    p = 1
    c = c3
}
one sig rule11 extends Rule{}{
    s =s10
    t =r13
    m = prohibition
    p = 3
    c = c4+c2+c5
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
