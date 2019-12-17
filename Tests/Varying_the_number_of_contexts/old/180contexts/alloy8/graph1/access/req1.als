module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s2+
         s4->s3+
         s5->s4+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s4+
         s8->s4+
         s9->s3+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s5+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s4+
         s18->s5+
         s18->s9+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s1+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s14+
         s21->s16+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s17+
         s22->s21+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s6+
         s23->s9+
         s23->s15+
         s23->s17+
         s23->s19+
         s23->s21+
         s23->s22+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s8+
         s25->s9+
         s25->s12+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s0+
         s26->s3+
         s26->s8+
         s26->s9+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s20+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s3+
         s28->s6+
         s28->s8+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s18+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s4+
         s29->s9+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r3+
         r12->r4+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r6+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r9+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r11+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r13+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r2+
         r20->r5+
         r20->r7+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r19+
         r21->r0+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r9+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r18+
         r21->r20+
         r22->r2+
         r22->r3+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r12+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r5+
         r23->r6+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r24->r0+
         r24->r1+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r19+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r8+
         r26->r11+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r4+
         r27->r5+
         r27->r9+
         r27->r10+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r22+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r2+
         r28->r3+
         r28->r6+
         r28->r7+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r17+
         r28->r18+
         r28->r22+
         r28->r23+
         r28->r24+
         r29->r0+
         r29->r2+
         r29->r3+
         r29->r7+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r23+
         r29->r25}

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
    s =s11
    t =r8
    m = permission
    p = 1
    c = c4+c8+c2+c0+c3+c1
}
one sig rule1 extends Rule{}{
    s =s10
    t =r15
    m = permission
    p = 2
    c = c4+c7+c5+c6
}
one sig rule2 extends Rule{}{
    s =s29
    t =r14
    m = prohibition
    p = 3
    c = c0+c4+c3
}
one sig rule3 extends Rule{}{
    s =s20
    t =r22
    m = permission
    p = 1
    c = c5+c8+c3+c1+c7
}
one sig rule4 extends Rule{}{
    s =s17
    t =r13
    m = prohibition
    p = 1
    c = c4
}
one sig rule5 extends Rule{}{
    s =s25
    t =r2
    m = prohibition
    p = 0
    c = c5+c3+c6+c0+c8+c2
}
one sig rule6 extends Rule{}{
    s =s29
    t =r29
    m = prohibition
    p = 0
    c = c9+c5+c6+c3+c4+c8+c1
}
one sig rule7 extends Rule{}{
    s =s26
    t =r26
    m = permission
    p = 2
    c = c7+c4+c1+c9+c5+c3+c2+c8
}
one sig rule8 extends Rule{}{
    s =s18
    t =r19
    m = permission
    p = 1
    c = c7+c9+c8+c0+c5+c1+c3
}
one sig rule9 extends Rule{}{
    s =s17
    t =r25
    m = prohibition
    p = 0
    c = c0+c5+c2+c8+c1+c3
}
one sig rule10 extends Rule{}{
    s =s27
    t =r27
    m = permission
    p = 3
    c = c5
}
one sig rule11 extends Rule{}{
    s =s2
    t =r24
    m = permission
    p = 4
    c = c6+c2+c3+c7
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
