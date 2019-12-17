module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
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
         s4->s2+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s4+
         s7->s3+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s4+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s8+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s4+
         s18->s6+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s1+
         s20->s3+
         s20->s5+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s4+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s16+
         s21->s19+
         s22->s0+
         s22->s4+
         s22->s6+
         s22->s10+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s20+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s14+
         s23->s17+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s2+
         s24->s4+
         s24->s6+
         s24->s7+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s18+
         s24->s21+
         s24->s22+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s9+
         s25->s12+
         s25->s13+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s8+
         s26->s9+
         s26->s13+
         s26->s16+
         s26->s17+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s10+
         s27->s15+
         s27->s16+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s26+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s18+
         s28->s20+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s13+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s21+
         s29->s25+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r5->r1+
         r5->r2+
         r6->r1+
         r6->r2+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r7+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r4+
         r15->r5+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r2+
         r16->r5+
         r16->r7+
         r16->r11+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r9+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r18+
         r20->r0+
         r20->r3+
         r20->r6+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r2+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r15+
         r22->r17+
         r22->r18+
         r23->r0+
         r23->r1+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r9+
         r23->r11+
         r23->r12+
         r23->r17+
         r23->r20+
         r23->r21+
         r24->r1+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r16+
         r24->r17+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r15+
         r25->r16+
         r25->r18+
         r25->r20+
         r25->r24+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r7+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r25+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r16+
         r27->r18+
         r27->r23+
         r27->r26+
         r28->r1+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r16+
         r28->r22+
         r28->r24+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r7+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r21+
         r29->r22+
         r29->r24+
         r29->r25+
         r29->r26+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8 extends Context{}{}

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
    s =s3
    t =r3
    m = prohibition
    p = 1
    c = c8+c0+c7+c4
}
one sig rule1 extends Rule{}{
    s =s8
    t =r7
    m = permission
    p = 1
    c = c6
}
one sig rule2 extends Rule{}{
    s =s18
    t =r12
    m = prohibition
    p = 2
    c = c7+c0+c2+c5+c4+c6+c8
}
one sig rule3 extends Rule{}{
    s =s9
    t =r22
    m = permission
    p = 1
    c = c0+c7+c8+c3
}
one sig rule4 extends Rule{}{
    s =s24
    t =r6
    m = permission
    p = 1
    c = c8+c1+c7+c6
}
one sig rule5 extends Rule{}{
    s =s9
    t =r7
    m = prohibition
    p = 0
    c = c7+c0
}
one sig rule6 extends Rule{}{
    s =s11
    t =r28
    m = permission
    p = 2
    c = c1+c7+c3
}
one sig rule7 extends Rule{}{
    s =s0
    t =r1
    m = prohibition
    p = 2
    c = c1+c2+c3+c4+c6+c7
}
one sig rule8 extends Rule{}{
    s =s12
    t =r5
    m = permission
    p = 1
    c = c8
}
one sig rule9 extends Rule{}{
    s =s8
    t =r14
    m = permission
    p = 2
    c = c5+c7+c8+c1
}
one sig rule10 extends Rule{}{
    s =s8
    t =r15
    m = prohibition
    p = 1
    c = c5+c7+c3
}
one sig rule11 extends Rule{}{
    s =s2
    t =r14
    m = prohibition
    p = 1
    c = c7+c8
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
