module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s4->s0+
         s5->s0+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s4+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s0+
         s11->s3+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s6+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s5+
         s15->s7+
         s15->s9+
         s15->s11+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s6+
         s17->s11+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s15+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s14+
         s19->s18+
         s20->s1+
         s20->s3+
         s20->s5+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s17+
         s21->s3+
         s21->s6+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s13+
         s21->s16+
         s21->s18+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s21+
         s23->s1+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s10+
         s23->s14+
         s23->s16+
         s23->s18+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s2+
         s24->s4+
         s24->s5+
         s24->s10+
         s24->s14+
         s24->s15+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s23+
         s25->s0+
         s25->s4+
         s25->s5+
         s25->s7+
         s25->s12+
         s25->s16+
         s25->s18+
         s25->s21+
         s26->s0+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s14+
         s26->s17+
         s26->s18+
         s26->s22+
         s26->s23+
         s26->s24+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s9+
         s27->s12+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s26+
         s28->s1+
         s28->s4+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s18+
         s28->s19+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s12+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s22+
         s29->s24+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r2+
         r6->r3+
         r6->r5+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r7+
         r15->r12+
         r15->r13+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r15+
         r17->r1+
         r17->r4+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r8+
         r18->r9+
         r18->r14+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r8+
         r19->r11+
         r19->r16+
         r20->r0+
         r20->r2+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r3+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r13+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r4+
         r22->r8+
         r22->r10+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r18+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r8+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r16+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r3+
         r24->r8+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r20+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r4+
         r25->r5+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r8+
         r26->r13+
         r26->r15+
         r26->r16+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r8+
         r27->r10+
         r27->r13+
         r27->r15+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r23+
         r27->r24+
         r28->r0+
         r28->r9+
         r28->r10+
         r28->r12+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r20+
         r28->r21+
         r28->r24+
         r28->r25+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r7+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r17+
         r29->r20+
         r29->r21+
         r29->r23+
         r29->r24+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r8
    m = prohibition
    p = 4
    c = c1+c3+c0+c9+c6+c8+c5
}
one sig rule1 extends Rule{}{
    s =s26
    t =r6
    m = prohibition
    p = 2
    c = c9+c1+c7+c6
}
one sig rule2 extends Rule{}{
    s =s1
    t =r5
    m = permission
    p = 3
    c = c8+c3+c2+c0+c4
}
one sig rule3 extends Rule{}{
    s =s29
    t =r0
    m = prohibition
    p = 0
    c = c7+c6
}
one sig rule4 extends Rule{}{
    s =s24
    t =r28
    m = prohibition
    p = 1
    c = c6
}
one sig rule5 extends Rule{}{
    s =s1
    t =r14
    m = permission
    p = 1
    c = c0+c5+c2+c4+c1+c7
}
one sig rule6 extends Rule{}{
    s =s17
    t =r29
    m = permission
    p = 2
    c = c9+c6+c5
}
one sig rule7 extends Rule{}{
    s =s18
    t =r15
    m = prohibition
    p = 2
    c = c5+c4+c8+c2+c9
}
one sig rule8 extends Rule{}{
    s =s20
    t =r15
    m = permission
    p = 3
    c = c0+c4
}
one sig rule9 extends Rule{}{
    s =s0
    t =r6
    m = permission
    p = 0
    c = c5+c4
}
one sig rule10 extends Rule{}{
    s =s0
    t =r20
    m = prohibition
    p = 0
    c = c2+c5
}
one sig rule11 extends Rule{}{
    s =s20
    t =r29
    m = prohibition
    p = 2
    c = c1+c7+c4+c5+c3+c6
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
