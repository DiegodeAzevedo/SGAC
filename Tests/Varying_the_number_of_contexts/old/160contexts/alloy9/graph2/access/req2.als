module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s2+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s4+
         s9->s2+
         s9->s4+
         s9->s6+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s2+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s12+
         s14->s2+
         s14->s13+
         s15->s2+
         s15->s5+
         s15->s7+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s15+
         s17->s16+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s12+
         s20->s13+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s5+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s15+
         s21->s17+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s19+
         s22->s20+
         s23->s2+
         s23->s4+
         s23->s11+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s19+
         s23->s22+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s8+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s15+
         s25->s18+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s0+
         s26->s2+
         s26->s6+
         s26->s10+
         s26->s11+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s3+
         s27->s6+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s21+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r4->r1+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r4+
         r8->r1+
         r8->r3+
         r8->r5+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r12->r1+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r8+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r8+
         r18->r9+
         r18->r10+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r11+
         r19->r14+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r18+
         r21->r1+
         r21->r3+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r9+
         r22->r11+
         r22->r17+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r1+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r20+
         r24->r6+
         r24->r7+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r15+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r19+
         r25->r20+
         r25->r24+
         r26->r1+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r11+
         r26->r13+
         r26->r14+
         r26->r17+
         r26->r19+
         r26->r21+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r18+
         r27->r19+
         r27->r22+
         r27->r23+
         r27->r24+
         r28->r0+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r8+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r15+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r23+
         r28->r24+
         r28->r26+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r16+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r26+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r9
    m = prohibition
    p = 2
    c = c7+c0+c9+c3
}
one sig rule1 extends Rule{}{
    s =s26
    t =r6
    m = prohibition
    p = 2
    c = c4+c9+c7+c6+c2+c1
}
one sig rule2 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 3
    c = c0+c8+c4+c7+c1+c9
}
one sig rule3 extends Rule{}{
    s =s24
    t =r20
    m = prohibition
    p = 0
    c = c5+c2+c0+c6
}
one sig rule4 extends Rule{}{
    s =s15
    t =r24
    m = prohibition
    p = 0
    c = c8+c1+c5+c2
}
one sig rule5 extends Rule{}{
    s =s21
    t =r14
    m = permission
    p = 4
    c = c5+c4+c6+c3+c7+c2
}
one sig rule6 extends Rule{}{
    s =s4
    t =r25
    m = permission
    p = 1
    c = c4+c5+c7+c1
}
one sig rule7 extends Rule{}{
    s =s19
    t =r10
    m = prohibition
    p = 0
    c = c1+c3+c5+c7+c9+c0
}
one sig rule8 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 0
    c = c9+c0+c5+c2+c8+c7
}
one sig rule9 extends Rule{}{
    s =s29
    t =r14
    m = prohibition
    p = 1
    c = c5+c6+c3+c0+c2
}
one sig rule10 extends Rule{}{
    s =s1
    t =r7
    m = permission
    p = 3
    c = c6+c3+c8+c2+c0+c9
}
one sig rule11 extends Rule{}{
    s =s7
    t =r12
    m = permission
    p = 2
    c = c9+c4+c0+c7
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
run accessReq2_c0{access_condition[req2,c0]} for 4
run accessReq2_c1{access_condition[req2,c1]} for 4
run accessReq2_c2{access_condition[req2,c2]} for 4
run accessReq2_c3{access_condition[req2,c3]} for 4
run accessReq2_c4{access_condition[req2,c4]} for 4
run accessReq2_c5{access_condition[req2,c5]} for 4
run accessReq2_c6{access_condition[req2,c6]} for 4
run accessReq2_c7{access_condition[req2,c7]} for 4
run accessReq2_c8{access_condition[req2,c8]} for 4
run accessReq2_c9{access_condition[req2,c9]} for 4
