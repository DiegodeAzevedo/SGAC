module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s4->s2+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s3+
         s7->s0+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s5+
         s13->s6+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s4+
         s15->s9+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s11+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s14+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s11+
         s18->s14+
         s19->s1+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s12+
         s19->s15+
         s19->s17+
         s20->s3+
         s20->s6+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s19+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s17+
         s21->s18+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s24->s11+
         s24->s14+
         s24->s15+
         s24->s17+
         s24->s19+
         s24->s22+
         s24->s23+
         s25->s2+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s22+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s23+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s19+
         s27->s21+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s6+
         s29->s8+
         s29->s9+
         s29->s12+
         s29->s14+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s25+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r5->r4+
         r7->r0+
         r7->r2+
         r7->r4+
         r8->r0+
         r8->r4+
         r8->r6+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r7+
         r10->r9+
         r11->r7+
         r12->r1+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r11+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r9+
         r14->r10+
         r14->r11+
         r15->r0+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r2+
         r20->r7+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r18+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r7+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r19+
         r21->r20+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r9+
         r22->r10+
         r22->r14+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r0+
         r23->r3+
         r23->r5+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r6+
         r24->r12+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r18+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r8+
         r25->r10+
         r25->r11+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r11+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r21+
         r26->r23+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r14+
         r27->r16+
         r27->r18+
         r27->r21+
         r27->r22+
         r27->r26+
         r28->r0+
         r28->r4+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r23+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r10+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r18+
         r29->r20+
         r29->r21+
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
one sig req5 extends Request{}{
sub=s1
res=r6
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s27
    t =r18
    m = permission
    p = 1
    c = c0+c6+c1+c3
}
one sig rule1 extends Rule{}{
    s =s25
    t =r28
    m = permission
    p = 0
    c = c4+c6+c9+c0+c7+c5+c2
}
one sig rule2 extends Rule{}{
    s =s27
    t =r22
    m = prohibition
    p = 1
    c = c3+c4+c8+c9+c6+c7
}
one sig rule3 extends Rule{}{
    s =s12
    t =r21
    m = prohibition
    p = 3
    c = c6+c1+c8+c0
}
one sig rule4 extends Rule{}{
    s =s27
    t =r11
    m = prohibition
    p = 3
    c = c8+c5+c1+c9+c2
}
one sig rule5 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 1
    c = c4+c0+c5+c8+c1
}
one sig rule6 extends Rule{}{
    s =s17
    t =r28
    m = prohibition
    p = 1
    c = c6+c7+c8+c2+c3
}
one sig rule7 extends Rule{}{
    s =s2
    t =r29
    m = permission
    p = 0
    c = c7
}
one sig rule8 extends Rule{}{
    s =s18
    t =r25
    m = prohibition
    p = 4
    c = c5
}
one sig rule9 extends Rule{}{
    s =s21
    t =r26
    m = permission
    p = 3
    c = c5+c8+c3+c4+c0
}
one sig rule10 extends Rule{}{
    s =s28
    t =r6
    m = prohibition
    p = 2
    c = c0+c6+c3
}
one sig rule11 extends Rule{}{
    s =s10
    t =r28
    m = prohibition
    p = 2
    c = c9+c6+c0+c3+c7
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
