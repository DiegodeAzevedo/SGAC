module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s6+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s3+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s12->s0+
         s12->s2+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s4+
         s15->s6+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s9+
         s18->s11+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s10+
         s20->s13+
         s20->s16+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s9+
         s21->s12+
         s21->s15+
         s21->s16+
         s21->s18+
         s21->s19+
         s22->s1+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s7+
         s24->s9+
         s24->s11+
         s24->s13+
         s24->s21+
         s25->s0+
         s25->s1+
         s25->s3+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s15+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s5+
         s26->s6+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s15+
         s26->s17+
         s26->s22+
         s26->s25+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s14+
         s27->s15+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s1+
         s28->s3+
         s28->s11+
         s28->s13+
         s28->s14+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s27+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s13+
         s29->s14+
         s29->s18+
         s29->s21+
         s29->s23+
         s29->s24+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r0+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r6+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r7+
         r11->r8+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r12+
         r16->r3+
         r16->r6+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r5+
         r19->r8+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r7+
         r20->r8+
         r20->r10+
         r20->r14+
         r20->r16+
         r20->r18+
         r20->r19+
         r21->r4+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r18+
         r22->r20+
         r22->r21+
         r23->r4+
         r23->r6+
         r23->r9+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r15+
         r23->r17+
         r23->r22+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r8+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r18+
         r24->r19+
         r24->r20+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r15+
         r25->r19+
         r25->r21+
         r25->r23+
         r26->r0+
         r26->r5+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r24+
         r26->r25+
         r27->r2+
         r27->r8+
         r27->r12+
         r27->r20+
         r27->r21+
         r27->r24+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r5+
         r28->r7+
         r28->r11+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r20+
         r28->r21+
         r28->r25+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r11+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r23+
         r29->r24+
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
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s26
    t =r27
    m = prohibition
    p = 0
    c = c4
}
one sig rule1 extends Rule{}{
    s =s9
    t =r20
    m = permission
    p = 0
    c = c7+c6+c4
}
one sig rule2 extends Rule{}{
    s =s6
    t =r8
    m = permission
    p = 3
    c = c9+c4+c7
}
one sig rule3 extends Rule{}{
    s =s24
    t =r25
    m = permission
    p = 0
    c = c9+c7+c8
}
one sig rule4 extends Rule{}{
    s =s17
    t =r18
    m = prohibition
    p = 4
    c = c9+c8+c1+c3
}
one sig rule5 extends Rule{}{
    s =s23
    t =r12
    m = permission
    p = 4
    c = c1+c4
}
one sig rule6 extends Rule{}{
    s =s9
    t =r25
    m = permission
    p = 1
    c = c5+c0
}
one sig rule7 extends Rule{}{
    s =s18
    t =r6
    m = prohibition
    p = 3
    c = c6+c8+c1+c2+c0+c5
}
one sig rule8 extends Rule{}{
    s =s28
    t =r26
    m = permission
    p = 0
    c = c9+c6
}
one sig rule9 extends Rule{}{
    s =s25
    t =r5
    m = prohibition
    p = 3
    c = c1+c8+c3+c6
}
one sig rule10 extends Rule{}{
    s =s13
    t =r20
    m = prohibition
    p = 1
    c = c7+c5+c1+c6+c8
}
one sig rule11 extends Rule{}{
    s =s11
    t =r24
    m = permission
    p = 0
    c = c4+c7+c2+c3+c1
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
