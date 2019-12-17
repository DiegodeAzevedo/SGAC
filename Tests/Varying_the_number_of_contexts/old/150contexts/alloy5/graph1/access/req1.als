module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s4->s1+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s5+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s9+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s8+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s2+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s3+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s10+
         s18->s11+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s3+
         s19->s7+
         s19->s8+
         s19->s11+
         s19->s12+
         s19->s17+
         s19->s18+
         s20->s2+
         s20->s3+
         s20->s6+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s15+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s15+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s8+
         s22->s9+
         s22->s14+
         s22->s15+
         s22->s17+
         s22->s19+
         s22->s20+
         s23->s0+
         s23->s2+
         s23->s5+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s10+
         s24->s13+
         s24->s14+
         s24->s17+
         s24->s18+
         s24->s20+
         s24->s21+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s7+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s22+
         s26->s0+
         s26->s2+
         s26->s10+
         s26->s13+
         s26->s15+
         s26->s18+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s6+
         s27->s9+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s19+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s4+
         s28->s7+
         s28->s12+
         s28->s14+
         s28->s16+
         s28->s18+
         s28->s20+
         s28->s21+
         s28->s23+
         s28->s24+
         s28->s26+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s6+
         s29->s8+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s25+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r6+
         r9->r7+
         r10->r3+
         r10->r4+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r7+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r10+
         r17->r3+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r14+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r13+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r20+
         r22->r8+
         r22->r9+
         r22->r14+
         r22->r17+
         r22->r19+
         r23->r0+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r19+
         r23->r21+
         r24->r0+
         r24->r5+
         r24->r10+
         r24->r12+
         r24->r14+
         r24->r16+
         r24->r18+
         r24->r19+
         r24->r20+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r10+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r4+
         r26->r5+
         r26->r8+
         r26->r11+
         r26->r12+
         r26->r16+
         r26->r18+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r6+
         r27->r7+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r16+
         r28->r18+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r13+
         r29->r15+
         r29->r18+
         r29->r19+
         r29->r21+
         r29->r23+
         r29->r28}

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
    s =s23
    t =r22
    m = permission
    p = 0
    c = c5+c7+c2+c8+c0
}
one sig rule1 extends Rule{}{
    s =s10
    t =r20
    m = permission
    p = 3
    c = c6+c7+c2+c4
}
one sig rule2 extends Rule{}{
    s =s15
    t =r28
    m = permission
    p = 2
    c = c2+c0+c8
}
one sig rule3 extends Rule{}{
    s =s19
    t =r29
    m = prohibition
    p = 3
    c = c0+c3+c5
}
one sig rule4 extends Rule{}{
    s =s11
    t =r9
    m = permission
    p = 3
    c = c6
}
one sig rule5 extends Rule{}{
    s =s19
    t =r21
    m = prohibition
    p = 2
    c = c1+c4+c7+c0+c8
}
one sig rule6 extends Rule{}{
    s =s8
    t =r16
    m = permission
    p = 4
    c = c1
}
one sig rule7 extends Rule{}{
    s =s13
    t =r28
    m = prohibition
    p = 4
    c = c0+c6+c9+c4+c5
}
one sig rule8 extends Rule{}{
    s =s11
    t =r23
    m = prohibition
    p = 1
    c = c3+c0+c8+c5
}
one sig rule9 extends Rule{}{
    s =s27
    t =r13
    m = permission
    p = 3
    c = c2
}
one sig rule10 extends Rule{}{
    s =s14
    t =r6
    m = prohibition
    p = 4
    c = c6+c7
}
one sig rule11 extends Rule{}{
    s =s28
    t =r15
    m = prohibition
    p = 4
    c = c5+c8+c1+c2+c0
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
