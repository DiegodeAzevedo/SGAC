module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s0+
         s7->s1+
         s7->s5+
         s8->s1+
         s8->s3+
         s8->s4+
         s9->s1+
         s9->s3+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s2+
         s14->s4+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s9+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s2+
         s18->s4+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s14+
         s19->s2+
         s19->s8+
         s19->s12+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s18+
         s22->s2+
         s22->s5+
         s22->s6+
         s22->s9+
         s22->s20+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s10+
         s23->s11+
         s23->s16+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s2+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s11+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s18+
         s24->s19+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s15+
         s25->s18+
         s25->s19+
         s25->s24+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s22+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s2+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s9+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s18+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s26+
         s28->s2+
         s28->s3+
         s28->s6+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s20+
         s28->s22+
         s28->s24+
         s28->s27+
         s29->s0+
         s29->s3+
         s29->s4+
         s29->s6+
         s29->s9+
         s29->s11+
         s29->s13+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r4->r0+
         r4->r3+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r3+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r3+
         r11->r4+
         r11->r6+
         r12->r0+
         r12->r3+
         r12->r6+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r7+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r11+
         r19->r13+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r4+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r15+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r4+
         r21->r5+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r18+
         r21->r20+
         r22->r0+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r10+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r1+
         r23->r3+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r20+
         r25->r0+
         r25->r1+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r9+
         r25->r11+
         r25->r14+
         r25->r16+
         r25->r18+
         r25->r20+
         r25->r23+
         r26->r2+
         r26->r3+
         r26->r6+
         r26->r8+
         r26->r9+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r20+
         r26->r21+
         r26->r24+
         r27->r0+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r1+
         r28->r3+
         r28->r6+
         r28->r8+
         r28->r14+
         r28->r16+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r26+
         r29->r5+
         r29->r7+
         r29->r9+
         r29->r11+
         r29->r15+
         r29->r17+
         r29->r21+
         r29->r22+
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
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s22
    t =r13
    m = permission
    p = 2
    c = c8
}
one sig rule1 extends Rule{}{
    s =s7
    t =r24
    m = permission
    p = 1
    c = c3+c9+c6+c4+c7+c0
}
one sig rule2 extends Rule{}{
    s =s8
    t =r22
    m = prohibition
    p = 1
    c = c9+c3+c4+c6+c0
}
one sig rule3 extends Rule{}{
    s =s23
    t =r20
    m = prohibition
    p = 3
    c = c2+c6+c7+c4+c8+c9
}
one sig rule4 extends Rule{}{
    s =s4
    t =r6
    m = permission
    p = 4
    c = c6
}
one sig rule5 extends Rule{}{
    s =s6
    t =r17
    m = prohibition
    p = 0
    c = c5+c8+c7
}
one sig rule6 extends Rule{}{
    s =s21
    t =r21
    m = permission
    p = 4
    c = c0+c8
}
one sig rule7 extends Rule{}{
    s =s19
    t =r0
    m = prohibition
    p = 2
    c = c9+c7+c4+c6+c3+c2
}
one sig rule8 extends Rule{}{
    s =s12
    t =r19
    m = permission
    p = 1
    c = c7+c8+c1+c5
}
one sig rule9 extends Rule{}{
    s =s3
    t =r11
    m = prohibition
    p = 4
    c = c9+c6+c7
}
one sig rule10 extends Rule{}{
    s =s21
    t =r1
    m = permission
    p = 2
    c = c1+c4
}
one sig rule11 extends Rule{}{
    s =s3
    t =r21
    m = permission
    p = 3
    c = c4+c8+c9+c1+c0
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
