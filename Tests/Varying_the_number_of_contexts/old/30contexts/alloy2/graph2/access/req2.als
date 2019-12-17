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
         s5->s0+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s5+
         s12->s7+
         s12->s10+
         s13->s1+
         s13->s3+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s10+
         s15->s11+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s14+
         s17->s2+
         s17->s5+
         s17->s10+
         s17->s11+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s4+
         s18->s10+
         s18->s12+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s10+
         s19->s13+
         s19->s17+
         s20->s2+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s21->s1+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s7+
         s21->s10+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s8+
         s23->s10+
         s23->s11+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s10+
         s24->s12+
         s24->s14+
         s24->s17+
         s24->s20+
         s24->s21+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s4+
         s25->s7+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s8+
         s26->s11+
         s26->s13+
         s26->s15+
         s26->s19+
         s26->s20+
         s26->s22+
         s26->s23+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s10+
         s27->s11+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s22+
         s27->s23+
         s28->s0+
         s28->s4+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s12+
         s28->s18+
         s28->s19+
         s28->s21+
         s28->s25+
         s29->s1+
         s29->s2+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r4->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r4+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r2+
         r12->r7+
         r12->r11+
         r13->r5+
         r13->r8+
         r14->r0+
         r14->r3+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r15+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r13+
         r20->r15+
         r20->r16+
         r20->r19+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r15+
         r21->r17+
         r21->r19+
         r22->r0+
         r22->r5+
         r22->r8+
         r22->r9+
         r22->r13+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r12+
         r23->r14+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r13+
         r24->r15+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r14+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r12+
         r26->r18+
         r26->r21+
         r26->r22+
         r26->r24+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r6+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r20+
         r27->r24+
         r27->r26+
         r28->r2+
         r28->r6+
         r28->r7+
         r28->r9+
         r28->r10+
         r28->r13+
         r28->r14+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r26+
         r29->r1+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r9+
         r29->r11+
         r29->r13+
         r29->r16+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r23+
         r29->r24+
         r29->r26+
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
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s27
    t =r11
    m = permission
    p = 0
    c = c0+c8+c2+c5+c6+c7
}
one sig rule1 extends Rule{}{
    s =s19
    t =r0
    m = prohibition
    p = 4
    c = c0+c3+c8+c7+c9+c4+c2+c5
}
one sig rule2 extends Rule{}{
    s =s19
    t =r1
    m = prohibition
    p = 1
    c = c8+c3+c6+c2+c9+c4+c1
}
one sig rule3 extends Rule{}{
    s =s0
    t =r27
    m = permission
    p = 2
    c = c1+c8+c9
}
one sig rule4 extends Rule{}{
    s =s25
    t =r19
    m = permission
    p = 4
    c = c1+c6+c8+c5
}
one sig rule5 extends Rule{}{
    s =s2
    t =r15
    m = permission
    p = 4
    c = c7+c9
}
one sig rule6 extends Rule{}{
    s =s4
    t =r27
    m = permission
    p = 4
    c = c6
}
one sig rule7 extends Rule{}{
    s =s23
    t =r23
    m = permission
    p = 4
    c = c3
}
one sig rule8 extends Rule{}{
    s =s0
    t =r20
    m = permission
    p = 2
    c = c2+c8+c1+c3+c5+c0+c7
}
one sig rule9 extends Rule{}{
    s =s13
    t =r26
    m = permission
    p = 1
    c = c7+c6+c2
}
one sig rule10 extends Rule{}{
    s =s0
    t =r5
    m = permission
    p = 0
    c = c2+c0+c5+c1+c9
}
one sig rule11 extends Rule{}{
    s =s13
    t =r5
    m = prohibition
    p = 3
    c = c9+c3+c8+c2+c6
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
