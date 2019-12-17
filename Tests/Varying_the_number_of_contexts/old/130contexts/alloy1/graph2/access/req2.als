module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s2+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s7->s0+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s7+
         s10->s2+
         s10->s4+
         s10->s6+
         s10->s8+
         s11->s0+
         s11->s3+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s7+
         s13->s10+
         s13->s12+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s11+
         s15->s3+
         s15->s7+
         s15->s8+
         s15->s12+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s12+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s9+
         s18->s13+
         s18->s14+
         s18->s15+
         s19->s0+
         s19->s1+
         s19->s7+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s20->s2+
         s20->s3+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s11+
         s21->s12+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s17+
         s22->s20+
         s23->s0+
         s23->s4+
         s23->s9+
         s23->s12+
         s23->s15+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s24->s2+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s8+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s23+
         s25->s1+
         s25->s4+
         s25->s6+
         s25->s9+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s0+
         s26->s3+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s13+
         s26->s17+
         s26->s19+
         s26->s20+
         s26->s22+
         s27->s0+
         s27->s2+
         s27->s8+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s17+
         s27->s19+
         s27->s23+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s3+
         s28->s5+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s29->s1+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r4+
         r7->r1+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r6+
         r12->r9+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r5+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r10+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r8+
         r17->r9+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r1+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r9+
         r20->r11+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r18+
         r21->r2+
         r21->r4+
         r21->r7+
         r21->r15+
         r21->r16+
         r21->r18+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r6+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r19+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r15+
         r23->r18+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r15+
         r24->r16+
         r24->r18+
         r24->r19+
         r24->r23+
         r25->r0+
         r25->r3+
         r25->r4+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r13+
         r25->r21+
         r25->r22+
         r26->r1+
         r26->r2+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r13+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r25+
         r27->r0+
         r27->r2+
         r27->r9+
         r27->r13+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r21+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r4+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r22+
         r29->r23}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s25
    t =r22
    m = prohibition
    p = 4
    c = c5+c4+c8+c1
}
one sig rule1 extends Rule{}{
    s =s29
    t =r4
    m = permission
    p = 3
    c = c8
}
one sig rule2 extends Rule{}{
    s =s19
    t =r1
    m = permission
    p = 3
    c = c6+c7+c4+c0
}
one sig rule3 extends Rule{}{
    s =s4
    t =r0
    m = permission
    p = 3
    c = c9
}
one sig rule4 extends Rule{}{
    s =s29
    t =r22
    m = permission
    p = 4
    c = c3+c0+c2+c6+c9
}
one sig rule5 extends Rule{}{
    s =s18
    t =r26
    m = permission
    p = 3
    c = c6+c2+c9+c5+c0+c3
}
one sig rule6 extends Rule{}{
    s =s24
    t =r0
    m = prohibition
    p = 0
    c = c6+c9+c2+c3
}
one sig rule7 extends Rule{}{
    s =s20
    t =r23
    m = prohibition
    p = 4
    c = c9+c6+c2+c4+c8+c0
}
one sig rule8 extends Rule{}{
    s =s27
    t =r7
    m = prohibition
    p = 0
    c = c3+c7+c9+c1+c4+c8
}
one sig rule9 extends Rule{}{
    s =s14
    t =r22
    m = prohibition
    p = 0
    c = c9+c6
}
one sig rule10 extends Rule{}{
    s =s24
    t =r11
    m = permission
    p = 1
    c = c6+c9+c3+c2+c8+c7+c5
}
one sig rule11 extends Rule{}{
    s =s6
    t =r25
    m = prohibition
    p = 2
    c = c4
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
