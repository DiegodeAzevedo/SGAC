module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s2+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s9->s0+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s3+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s16->s2+
         s16->s5+
         s16->s7+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s4+
         s18->s11+
         s18->s12+
         s19->s0+
         s19->s1+
         s19->s5+
         s19->s6+
         s19->s11+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s18+
         s22->s21+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s10+
         s23->s12+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s21+
         s23->s22+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s6+
         s24->s8+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s21+
         s25->s1+
         s25->s2+
         s25->s6+
         s25->s7+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s18+
         s25->s23+
         s25->s24+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s18+
         s26->s21+
         s26->s23+
         s26->s25+
         s27->s1+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s10+
         s27->s12+
         s27->s18+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s4+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s13+
         s28->s15+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s22+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s8+
         s29->s10+
         s29->s12+
         s29->s14+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s25+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r7->r1+
         r7->r3+
         r8->r0+
         r8->r2+
         r8->r7+
         r9->r0+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r5+
         r12->r8+
         r12->r9+
         r13->r2+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r5+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r8+
         r15->r9+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r13+
         r17->r16+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r11+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r18+
         r20->r0+
         r20->r3+
         r20->r4+
         r20->r11+
         r20->r15+
         r20->r18+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r6+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r16+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r4+
         r22->r7+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r0+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r12+
         r23->r13+
         r23->r16+
         r23->r18+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r8+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r22+
         r25->r1+
         r25->r6+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r15+
         r25->r18+
         r25->r19+
         r25->r21+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r10+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r5+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r13+
         r27->r14+
         r27->r20+
         r27->r23+
         r27->r24+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r9+
         r28->r12+
         r28->r18+
         r28->r20+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r23+
         r29->r24+
         r29->r25+
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
    s =s5
    t =r14
    m = prohibition
    p = 3
    c = c5
}
one sig rule1 extends Rule{}{
    s =s25
    t =r13
    m = prohibition
    p = 2
    c = c9+c4+c3+c2
}
one sig rule2 extends Rule{}{
    s =s23
    t =r10
    m = prohibition
    p = 4
    c = c5
}
one sig rule3 extends Rule{}{
    s =s9
    t =r19
    m = permission
    p = 1
    c = c2+c9+c5+c7
}
one sig rule4 extends Rule{}{
    s =s29
    t =r25
    m = prohibition
    p = 1
    c = c8+c0+c2+c7+c3
}
one sig rule5 extends Rule{}{
    s =s7
    t =r1
    m = permission
    p = 0
    c = c7+c8+c0
}
one sig rule6 extends Rule{}{
    s =s9
    t =r24
    m = permission
    p = 4
    c = c9+c2+c0+c8+c4
}
one sig rule7 extends Rule{}{
    s =s15
    t =r21
    m = prohibition
    p = 1
    c = c9+c8+c5
}
one sig rule8 extends Rule{}{
    s =s2
    t =r5
    m = prohibition
    p = 0
    c = c2
}
one sig rule9 extends Rule{}{
    s =s9
    t =r19
    m = prohibition
    p = 1
    c = c4
}
one sig rule10 extends Rule{}{
    s =s1
    t =r27
    m = prohibition
    p = 0
    c = c7+c6+c2
}
one sig rule11 extends Rule{}{
    s =s12
    t =r1
    m = permission
    p = 4
    c = c1+c0+c6
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
