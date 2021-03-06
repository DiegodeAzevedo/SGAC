module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s2+
         s7->s1+
         s7->s2+
         s7->s3+
         s8->s1+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s5+
         s11->s1+
         s11->s5+
         s11->s7+
         s12->s1+
         s12->s2+
         s12->s9+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s12+
         s14->s2+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s12+
         s15->s0+
         s15->s6+
         s15->s9+
         s15->s12+
         s16->s0+
         s16->s2+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s3+
         s17->s7+
         s17->s11+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s13+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s13+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s4+
         s21->s9+
         s21->s14+
         s21->s15+
         s22->s0+
         s22->s3+
         s22->s6+
         s22->s9+
         s22->s14+
         s22->s16+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s8+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s7+
         s24->s11+
         s24->s12+
         s24->s15+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s23+
         s25->s4+
         s25->s5+
         s25->s7+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s24+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s25+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s17+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s25+
         s29->s2+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s12+
         s29->s16+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s25+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r5+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r9->r1+
         r9->r2+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r8+
         r14->r12+
         r15->r0+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r4+
         r17->r9+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r19+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r10+
         r21->r11+
         r21->r15+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r5+
         r22->r7+
         r22->r12+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r12+
         r24->r16+
         r24->r20+
         r24->r21+
         r24->r22+
         r25->r1+
         r25->r3+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r8+
         r26->r10+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r19+
         r26->r21+
         r27->r2+
         r27->r3+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r9+
         r28->r10+
         r28->r17+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r6+
         r29->r10+
         r29->r11+
         r29->r14+
         r29->r15+
         r29->r18+
         r29->r19+
         r29->r21+
         r29->r24+
         r29->r25+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r8
    m = prohibition
    p = 4
    c = c2+c9+c0+c8+c6+c3
}
one sig rule1 extends Rule{}{
    s =s14
    t =r2
    m = prohibition
    p = 1
    c = c4
}
one sig rule2 extends Rule{}{
    s =s29
    t =r7
    m = prohibition
    p = 4
    c = c4+c0+c9
}
one sig rule3 extends Rule{}{
    s =s28
    t =r5
    m = prohibition
    p = 4
    c = c7+c1+c4
}
one sig rule4 extends Rule{}{
    s =s6
    t =r28
    m = prohibition
    p = 1
    c = c3+c6+c7+c1
}
one sig rule5 extends Rule{}{
    s =s19
    t =r20
    m = permission
    p = 4
    c = c3+c9+c1+c5
}
one sig rule6 extends Rule{}{
    s =s12
    t =r18
    m = permission
    p = 0
    c = c0+c9+c7+c5+c3+c8
}
one sig rule7 extends Rule{}{
    s =s15
    t =r14
    m = prohibition
    p = 3
    c = c1+c9+c8+c0+c6+c5
}
one sig rule8 extends Rule{}{
    s =s19
    t =r26
    m = prohibition
    p = 1
    c = c1+c8+c9
}
one sig rule9 extends Rule{}{
    s =s17
    t =r25
    m = permission
    p = 1
    c = c6+c8+c2+c7
}
one sig rule10 extends Rule{}{
    s =s15
    t =r0
    m = prohibition
    p = 2
    c = c8+c5+c7+c3+c9+c4+c1
}
one sig rule11 extends Rule{}{
    s =s16
    t =r26
    m = prohibition
    p = 4
    c = c1+c4
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
