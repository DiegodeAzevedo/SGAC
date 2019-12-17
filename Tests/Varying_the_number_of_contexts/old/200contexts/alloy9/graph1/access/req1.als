module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s2+
         s10->s4+
         s10->s5+
         s10->s7+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s12->s0+
         s12->s2+
         s12->s6+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s7+
         s13->s9+
         s14->s0+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s9+
         s17->s1+
         s17->s3+
         s17->s8+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s9+
         s19->s10+
         s19->s16+
         s20->s0+
         s20->s1+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s14+
         s20->s16+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s14+
         s21->s15+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s17+
         s22->s18+
         s22->s19+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s10+
         s23->s12+
         s23->s14+
         s23->s18+
         s23->s21+
         s23->s22+
         s24->s1+
         s24->s2+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s15+
         s24->s16+
         s24->s22+
         s24->s23+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s18+
         s25->s19+
         s25->s23+
         s25->s24+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s9+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s18+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s5+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s26+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s17+
         s29->s18+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r10->r0+
         r10->r2+
         r10->r5+
         r10->r7+
         r10->r8+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r9+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r7+
         r15->r8+
         r15->r11+
         r15->r13+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r12+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r10+
         r18->r11+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r17+
         r19->r18+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r8+
         r20->r10+
         r20->r12+
         r20->r14+
         r20->r16+
         r20->r18+
         r20->r19+
         r21->r2+
         r21->r3+
         r21->r9+
         r21->r12+
         r21->r15+
         r21->r17+
         r21->r20+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r10+
         r22->r11+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r15+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r4+
         r24->r5+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r17+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r5+
         r25->r7+
         r25->r10+
         r25->r13+
         r25->r15+
         r25->r21+
         r25->r22+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r5+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r25+
         r28->r0+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r16+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r25+
         r28->r27+
         r29->r1+
         r29->r10+
         r29->r11+
         r29->r16+
         r29->r20+
         r29->r22+
         r29->r23+
         r29->r24+
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
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r7
    m = prohibition
    p = 1
    c = c7+c2
}
one sig rule1 extends Rule{}{
    s =s15
    t =r24
    m = permission
    p = 3
    c = c9+c4+c3
}
one sig rule2 extends Rule{}{
    s =s26
    t =r19
    m = permission
    p = 4
    c = c6+c3+c5+c1+c8+c9+c4
}
one sig rule3 extends Rule{}{
    s =s5
    t =r12
    m = prohibition
    p = 4
    c = c6+c3+c0+c9
}
one sig rule4 extends Rule{}{
    s =s15
    t =r23
    m = prohibition
    p = 1
    c = c8+c5+c4+c6+c1+c2
}
one sig rule5 extends Rule{}{
    s =s25
    t =r26
    m = permission
    p = 0
    c = c8+c9+c0
}
one sig rule6 extends Rule{}{
    s =s29
    t =r23
    m = prohibition
    p = 1
    c = c9+c0+c2
}
one sig rule7 extends Rule{}{
    s =s20
    t =r21
    m = prohibition
    p = 1
    c = c9+c3+c0+c2+c5
}
one sig rule8 extends Rule{}{
    s =s26
    t =r0
    m = prohibition
    p = 2
    c = c8+c0+c9
}
one sig rule9 extends Rule{}{
    s =s16
    t =r2
    m = permission
    p = 2
    c = c8+c6+c0+c2+c5
}
one sig rule10 extends Rule{}{
    s =s10
    t =r4
    m = prohibition
    p = 4
    c = c0
}
one sig rule11 extends Rule{}{
    s =s10
    t =r19
    m = prohibition
    p = 0
    c = c1+c0
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
