module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
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
         s5->s4+
         s6->s0+
         s6->s5+
         s7->s1+
         s7->s2+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s11+
         s15->s2+
         s15->s4+
         s15->s7+
         s15->s9+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s17->s0+
         s17->s3+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s9+
         s19->s14+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s8+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s20+
         s22->s21+
         s23->s2+
         s23->s3+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s18+
         s24->s0+
         s24->s1+
         s24->s5+
         s24->s7+
         s24->s9+
         s24->s14+
         s24->s16+
         s24->s18+
         s24->s21+
         s25->s2+
         s25->s7+
         s25->s8+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s4+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s11+
         s26->s14+
         s26->s17+
         s26->s18+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s0+
         s27->s2+
         s27->s5+
         s27->s6+
         s27->s10+
         s27->s13+
         s27->s14+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s23+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s24+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s1+
         s29->s4+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s13+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s23+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r2+
         r4->r3+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r11->r1+
         r11->r3+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r7+
         r12->r10+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r2+
         r14->r7+
         r14->r10+
         r15->r0+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r10+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r10+
         r16->r11+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r9+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r10+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r16+
         r21->r17+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r20+
         r22->r21+
         r23->r3+
         r23->r6+
         r23->r9+
         r23->r10+
         r23->r14+
         r23->r17+
         r23->r18+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r4+
         r24->r7+
         r24->r8+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r17+
         r24->r21+
         r25->r0+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r8+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r23+
         r26->r0+
         r26->r7+
         r26->r8+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r19+
         r26->r20+
         r26->r22+
         r26->r25+
         r27->r3+
         r27->r6+
         r27->r7+
         r27->r11+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r19+
         r27->r21+
         r27->r22+
         r27->r23+
         r28->r2+
         r28->r3+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r17+
         r28->r22+
         r28->r23+
         r29->r0+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r8+
         r29->r11+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r5
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s26
    t =r26
    m = prohibition
    p = 2
    c = c3+c6+c0+c5+c8+c1
}
one sig rule1 extends Rule{}{
    s =s6
    t =r11
    m = prohibition
    p = 1
    c = c9+c6+c2+c8+c0
}
one sig rule2 extends Rule{}{
    s =s6
    t =r21
    m = prohibition
    p = 0
    c = c6+c3+c1+c5+c2+c7+c4+c0
}
one sig rule3 extends Rule{}{
    s =s26
    t =r7
    m = prohibition
    p = 2
    c = c6+c2+c7+c4+c8+c5+c9
}
one sig rule4 extends Rule{}{
    s =s14
    t =r27
    m = permission
    p = 0
    c = c1+c4+c6+c5+c9
}
one sig rule5 extends Rule{}{
    s =s19
    t =r14
    m = permission
    p = 4
    c = c7+c8+c2+c1+c3+c9
}
one sig rule6 extends Rule{}{
    s =s26
    t =r3
    m = permission
    p = 3
    c = c7+c3+c0
}
one sig rule7 extends Rule{}{
    s =s4
    t =r2
    m = prohibition
    p = 1
    c = c9
}
one sig rule8 extends Rule{}{
    s =s25
    t =r26
    m = permission
    p = 1
    c = c3+c9+c5+c4+c1
}
one sig rule9 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 4
    c = c6+c8
}
one sig rule10 extends Rule{}{
    s =s7
    t =r14
    m = permission
    p = 1
    c = c1+c3
}
one sig rule11 extends Rule{}{
    s =s25
    t =r14
    m = prohibition
    p = 4
    c = c6+c2+c7
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
