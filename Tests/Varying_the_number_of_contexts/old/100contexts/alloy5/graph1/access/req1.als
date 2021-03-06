module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s3+
         s7->s5+
         s8->s1+
         s8->s2+
         s9->s1+
         s9->s2+
         s9->s7+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s8+
         s12->s0+
         s12->s4+
         s12->s5+
         s12->s9+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s11+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s9+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s6+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s8+
         s19->s10+
         s19->s13+
         s19->s16+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s16+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s10+
         s21->s15+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s20+
         s22->s21+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s8+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s18+
         s23->s19+
         s23->s21+
         s23->s22+
         s24->s2+
         s24->s4+
         s24->s5+
         s24->s12+
         s24->s13+
         s24->s20+
         s24->s22+
         s24->s23+
         s25->s3+
         s25->s4+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s17+
         s25->s19+
         s25->s24+
         s26->s0+
         s26->s3+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s24+
         s27->s1+
         s27->s2+
         s27->s5+
         s27->s6+
         s27->s9+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s18+
         s27->s20+
         s27->s23+
         s27->s25+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s15+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s5+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r3+
         r5->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r8->r2+
         r8->r3+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r5+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r5+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r10+
         r13->r12+
         r14->r2+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r9+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r8+
         r17->r10+
         r18->r0+
         r18->r1+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r13+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r18+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r8+
         r23->r11+
         r23->r12+
         r23->r15+
         r23->r17+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r8+
         r24->r12+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r8+
         r25->r10+
         r25->r12+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r5+
         r26->r8+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r20+
         r26->r21+
         r27->r2+
         r27->r3+
         r27->r6+
         r27->r9+
         r27->r12+
         r27->r13+
         r27->r15+
         r27->r20+
         r27->r25+
         r27->r26+
         r28->r2+
         r28->r3+
         r28->r6+
         r28->r7+
         r28->r9+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r22+
         r28->r25+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r15+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r24+
         r29->r25+
         r29->r26+
         r29->r27+
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
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r6
    m = prohibition
    p = 4
    c = c3+c5+c8+c7+c4+c0
}
one sig rule1 extends Rule{}{
    s =s3
    t =r4
    m = permission
    p = 4
    c = c4
}
one sig rule2 extends Rule{}{
    s =s27
    t =r16
    m = prohibition
    p = 0
    c = c3+c1+c2
}
one sig rule3 extends Rule{}{
    s =s22
    t =r8
    m = prohibition
    p = 1
    c = c8+c4+c3+c7+c9+c6+c5
}
one sig rule4 extends Rule{}{
    s =s16
    t =r9
    m = permission
    p = 0
    c = c6+c9+c8+c4+c0
}
one sig rule5 extends Rule{}{
    s =s14
    t =r8
    m = permission
    p = 0
    c = c2+c3+c1+c9
}
one sig rule6 extends Rule{}{
    s =s5
    t =r26
    m = prohibition
    p = 4
    c = c1+c9+c8+c4+c7+c2+c6
}
one sig rule7 extends Rule{}{
    s =s20
    t =r13
    m = prohibition
    p = 0
    c = c5+c1+c9+c2+c6+c0+c4
}
one sig rule8 extends Rule{}{
    s =s12
    t =r11
    m = permission
    p = 1
    c = c3+c5+c1+c2
}
one sig rule9 extends Rule{}{
    s =s23
    t =r5
    m = prohibition
    p = 0
    c = c1+c7+c3+c6
}
one sig rule10 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 0
    c = c1
}
one sig rule11 extends Rule{}{
    s =s25
    t =r2
    m = permission
    p = 3
    c = c2+c7+c3+c9+c6+c8
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
