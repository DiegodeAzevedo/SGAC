module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s1+
         s4->s1+
         s4->s2+
         s4->s3+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s7+
         s10->s9+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s11+
         s15->s0+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s10+
         s15->s11+
         s16->s5+
         s16->s11+
         s17->s0+
         s17->s1+
         s17->s5+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s7+
         s18->s9+
         s18->s13+
         s18->s14+
         s18->s15+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s2+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s13+
         s20->s15+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s15+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s2+
         s22->s5+
         s22->s6+
         s22->s10+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s22+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s19+
         s25->s1+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s19+
         s25->s21+
         s26->s0+
         s26->s3+
         s26->s4+
         s26->s6+
         s26->s10+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s18+
         s26->s19+
         s26->s20+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s6+
         s27->s7+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s19+
         s27->s22+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s1+
         s28->s3+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s14+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s23+
         s28->s24+
         s29->s0+
         s29->s1+
         s29->s4+
         s29->s5+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s15+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s23+
         s29->s24+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r2+
         r5->r0+
         r6->r5+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r3+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r5+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r3+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r8+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r9+
         r13->r10+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r11+
         r15->r12+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r15+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r16+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r4+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r19+
         r21->r20+
         r22->r2+
         r22->r3+
         r22->r7+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r16+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r13+
         r23->r17+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r21+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r13+
         r25->r14+
         r25->r15+
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
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r14+
         r27->r17+
         r27->r18+
         r27->r23+
         r27->r26+
         r28->r0+
         r28->r2+
         r28->r6+
         r28->r7+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r17+
         r28->r27+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r9+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r18+
         r29->r23+
         r29->r24+
         r29->r27}

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
    s =s1
    t =r29
    m = permission
    p = 2
    c = c2+c6+c1+c4+c8+c0
}
one sig rule1 extends Rule{}{
    s =s12
    t =r5
    m = permission
    p = 0
    c = c9+c0
}
one sig rule2 extends Rule{}{
    s =s10
    t =r16
    m = permission
    p = 3
    c = c2+c8
}
one sig rule3 extends Rule{}{
    s =s25
    t =r22
    m = permission
    p = 3
    c = c6+c9+c0+c3+c5+c7
}
one sig rule4 extends Rule{}{
    s =s25
    t =r26
    m = permission
    p = 0
    c = c3+c9+c5
}
one sig rule5 extends Rule{}{
    s =s7
    t =r23
    m = permission
    p = 4
    c = c5+c3+c8+c0+c9
}
one sig rule6 extends Rule{}{
    s =s15
    t =r19
    m = permission
    p = 4
    c = c8+c5+c3+c7+c9+c4
}
one sig rule7 extends Rule{}{
    s =s14
    t =r28
    m = prohibition
    p = 4
    c = c7+c6
}
one sig rule8 extends Rule{}{
    s =s14
    t =r18
    m = prohibition
    p = 0
    c = c8+c0+c1+c6+c5+c2+c3+c7
}
one sig rule9 extends Rule{}{
    s =s14
    t =r19
    m = prohibition
    p = 0
    c = c2+c3+c6
}
one sig rule10 extends Rule{}{
    s =s29
    t =r3
    m = prohibition
    p = 4
    c = c6
}
one sig rule11 extends Rule{}{
    s =s13
    t =r29
    m = prohibition
    p = 3
    c = c9+c7+c0+c4+c3+c2+c1
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
