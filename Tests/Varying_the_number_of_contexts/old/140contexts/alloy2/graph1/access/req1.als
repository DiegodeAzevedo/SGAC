module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s2+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s4+
         s11->s7+
         s11->s8+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s6+
         s17->s9+
         s17->s12+
         s17->s16+
         s18->s1+
         s18->s4+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s10+
         s19->s14+
         s19->s16+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s6+
         s20->s9+
         s20->s11+
         s20->s13+
         s20->s15+
         s20->s16+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s7+
         s21->s13+
         s21->s14+
         s21->s16+
         s21->s20+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s10+
         s22->s15+
         s22->s16+
         s22->s18+
         s22->s20+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s11+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s17+
         s24->s19+
         s24->s21+
         s24->s23+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s11+
         s25->s14+
         s25->s17+
         s25->s18+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s3+
         s26->s4+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s16+
         s26->s19+
         s26->s20+
         s26->s23+
         s26->s25+
         s27->s0+
         s27->s5+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s26+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s13+
         s28->s16+
         s28->s17+
         s28->s20+
         s28->s24+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s15+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r6->r1+
         r6->r2+
         r6->r4+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r7+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r7+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r3+
         r13->r6+
         r13->r10+
         r13->r12+
         r14->r2+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r12+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r9+
         r15->r11+
         r15->r13+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r9+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r12+
         r18->r15+
         r18->r17+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r10+
         r20->r11+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r22->r0+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r16+
         r22->r17+
         r22->r20+
         r22->r21+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r13+
         r23->r14+
         r23->r16+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r11+
         r24->r19+
         r24->r20+
         r25->r0+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r2+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r16+
         r26->r19+
         r26->r21+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r17+
         r27->r18+
         r27->r22+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r6+
         r28->r10+
         r28->r12+
         r28->r16+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r25+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r14+
         r29->r15+
         r29->r18+
         r29->r20+
         r29->r21+
         r29->r23}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r5
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s21
    t =r28
    m = prohibition
    p = 0
    c = c7+c6+c1+c5
}
one sig rule1 extends Rule{}{
    s =s10
    t =r14
    m = permission
    p = 3
    c = c6+c3+c5+c8+c2+c4
}
one sig rule2 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 4
    c = c5+c7
}
one sig rule3 extends Rule{}{
    s =s11
    t =r18
    m = prohibition
    p = 1
    c = c3+c5+c6+c4+c9+c2
}
one sig rule4 extends Rule{}{
    s =s5
    t =r11
    m = permission
    p = 0
    c = c9+c0+c7
}
one sig rule5 extends Rule{}{
    s =s21
    t =r25
    m = permission
    p = 0
    c = c2+c5+c6+c1+c4+c7
}
one sig rule6 extends Rule{}{
    s =s10
    t =r18
    m = permission
    p = 4
    c = c2+c7+c5+c6+c3+c4+c9
}
one sig rule7 extends Rule{}{
    s =s3
    t =r12
    m = prohibition
    p = 3
    c = c4+c3+c5
}
one sig rule8 extends Rule{}{
    s =s16
    t =r7
    m = prohibition
    p = 0
    c = c9+c8+c4
}
one sig rule9 extends Rule{}{
    s =s18
    t =r22
    m = permission
    p = 3
    c = c3+c7+c9
}
one sig rule10 extends Rule{}{
    s =s17
    t =r18
    m = permission
    p = 3
    c = c8
}
one sig rule11 extends Rule{}{
    s =s0
    t =r1
    m = prohibition
    p = 0
    c = c8+c0+c2+c7+c1
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
