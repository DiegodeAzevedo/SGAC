module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s5->s0+
         s5->s1+
         s6->s2+
         s6->s4+
         s7->s1+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s5+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s11->s1+
         s11->s2+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s10+
         s14->s0+
         s14->s3+
         s14->s6+
         s14->s10+
         s14->s11+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s5+
         s18->s8+
         s18->s11+
         s18->s13+
         s18->s17+
         s19->s2+
         s19->s4+
         s19->s8+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s18+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s7+
         s20->s9+
         s20->s11+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s2+
         s21->s5+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s17+
         s22->s19+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s21+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s17+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s6+
         s25->s10+
         s25->s12+
         s25->s15+
         s25->s19+
         s25->s21+
         s25->s22+
         s26->s0+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s8+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s23+
         s27->s0+
         s27->s1+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s23+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s9+
         s28->s12+
         s28->s21+
         s28->s22+
         s28->s24+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s20+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r3+
         r13->r7+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r5+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r10+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r20->r0+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r18+
         r21->r2+
         r21->r5+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r18+
         r21->r19+
         r22->r3+
         r22->r4+
         r22->r6+
         r22->r7+
         r22->r9+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r17+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r18+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r14+
         r24->r18+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r3+
         r25->r6+
         r25->r8+
         r25->r12+
         r25->r13+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r22+
         r26->r0+
         r26->r1+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r16+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r22+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r7+
         r27->r9+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r14+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r24+
         r27->r25+
         r28->r1+
         r28->r5+
         r28->r7+
         r28->r9+
         r28->r10+
         r28->r12+
         r28->r14+
         r28->r16+
         r28->r20+
         r28->r21+
         r28->r23+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r21+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s26
    t =r20
    m = prohibition
    p = 3
    c = c1+c3+c8
}
one sig rule1 extends Rule{}{
    s =s23
    t =r27
    m = permission
    p = 1
    c = c2+c0
}
one sig rule2 extends Rule{}{
    s =s18
    t =r2
    m = prohibition
    p = 3
    c = c1+c2+c5+c3
}
one sig rule3 extends Rule{}{
    s =s7
    t =r8
    m = permission
    p = 0
    c = c1+c7+c9+c4+c6
}
one sig rule4 extends Rule{}{
    s =s3
    t =r18
    m = prohibition
    p = 2
    c = c0+c5+c8+c4+c2
}
one sig rule5 extends Rule{}{
    s =s1
    t =r23
    m = prohibition
    p = 3
    c = c2+c0+c6+c9+c7
}
one sig rule6 extends Rule{}{
    s =s29
    t =r23
    m = prohibition
    p = 1
    c = c6
}
one sig rule7 extends Rule{}{
    s =s10
    t =r1
    m = prohibition
    p = 4
    c = c0+c2+c5+c1
}
one sig rule8 extends Rule{}{
    s =s7
    t =r9
    m = permission
    p = 4
    c = c5+c7+c8+c4+c9
}
one sig rule9 extends Rule{}{
    s =s6
    t =r26
    m = prohibition
    p = 1
    c = c3+c9+c6
}
one sig rule10 extends Rule{}{
    s =s28
    t =r17
    m = prohibition
    p = 3
    c = c8+c9
}
one sig rule11 extends Rule{}{
    s =s3
    t =r15
    m = prohibition
    p = 1
    c = c2+c8
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
run accessReq0_c0{access_condition[req0,c0]} for 4
run accessReq0_c1{access_condition[req0,c1]} for 4
run accessReq0_c2{access_condition[req0,c2]} for 4
run accessReq0_c3{access_condition[req0,c3]} for 4
run accessReq0_c4{access_condition[req0,c4]} for 4
run accessReq0_c5{access_condition[req0,c5]} for 4
run accessReq0_c6{access_condition[req0,c6]} for 4
run accessReq0_c7{access_condition[req0,c7]} for 4
run accessReq0_c8{access_condition[req0,c8]} for 4
run accessReq0_c9{access_condition[req0,c9]} for 4
