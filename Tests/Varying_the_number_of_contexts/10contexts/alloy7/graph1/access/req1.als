module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s1+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s1+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s7+
         s13->s8+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s13+
         s16->s2+
         s16->s3+
         s16->s7+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s13+
         s18->s4+
         s18->s6+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s9+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s19+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s10+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s18+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s5+
         s23->s6+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s16+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s7+
         s24->s10+
         s24->s12+
         s24->s14+
         s24->s17+
         s24->s19+
         s24->s22+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s7+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s1+
         s26->s2+
         s26->s8+
         s26->s9+
         s26->s11+
         s26->s15+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s23+
         s27->s2+
         s27->s4+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s15+
         s27->s19+
         s27->s22+
         s27->s26+
         s28->s3+
         s28->s4+
         s28->s6+
         s28->s8+
         s28->s10+
         s28->s12+
         s28->s17+
         s28->s20+
         s28->s22+
         s28->s24+
         s28->s25+
         s29->s0+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s15+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r5->r0+
         r5->r1+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r9->r2+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r4+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r6+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r12+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r17+
         r19->r1+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r16+
         r19->r17+
         r20->r0+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r15+
         r21->r1+
         r21->r2+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r13+
         r21->r14+
         r21->r16+
         r21->r17+
         r21->r19+
         r22->r1+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r21+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r6+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r15+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r3+
         r25->r5+
         r25->r6+
         r25->r12+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r8+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r5+
         r27->r9+
         r27->r14+
         r27->r15+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r26+
         r28->r0+
         r28->r2+
         r28->r4+
         r28->r7+
         r28->r8+
         r28->r10+
         r28->r11+
         r28->r13+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r22+
         r28->r25+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r18+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r25+
         r29->r26+
         r29->r27}

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
    s =s29
    t =r22
    m = prohibition
    p = 1
    c = c0
}
one sig rule1 extends Rule{}{
    s =s7
    t =r15
    m = permission
    p = 0
    c = c7+c9
}
one sig rule2 extends Rule{}{
    s =s18
    t =r9
    m = prohibition
    p = 4
    c = c0+c7+c3+c4+c6+c5+c8
}
one sig rule3 extends Rule{}{
    s =s20
    t =r29
    m = prohibition
    p = 4
    c = c0+c1
}
one sig rule4 extends Rule{}{
    s =s22
    t =r19
    m = permission
    p = 4
    c = c0+c1+c7+c9+c2+c4+c3+c8+c5
}
one sig rule5 extends Rule{}{
    s =s19
    t =r21
    m = prohibition
    p = 4
    c = c3+c5+c6+c2
}
one sig rule6 extends Rule{}{
    s =s3
    t =r2
    m = permission
    p = 4
    c = c5+c1+c6+c2+c0
}
one sig rule7 extends Rule{}{
    s =s17
    t =r26
    m = prohibition
    p = 2
    c = c1+c7+c9
}
one sig rule8 extends Rule{}{
    s =s18
    t =r10
    m = permission
    p = 1
    c = c3+c4+c9+c6+c8+c0+c7
}
one sig rule9 extends Rule{}{
    s =s9
    t =r10
    m = permission
    p = 1
    c = c5
}
one sig rule10 extends Rule{}{
    s =s27
    t =r9
    m = permission
    p = 4
    c = c0+c8+c7+c3
}
one sig rule11 extends Rule{}{
    s =s15
    t =r10
    m = permission
    p = 1
    c = c5+c4+c7
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
