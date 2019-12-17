module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s2+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s9+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s8+
         s13->s12+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s9+
         s15->s11+
         s15->s14+
         s16->s4+
         s16->s5+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s12+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s9+
         s18->s11+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17+
         s20->s0+
         s20->s2+
         s20->s3+
         s20->s6+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s14+
         s20->s16+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s6+
         s21->s8+
         s21->s11+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s19+
         s22->s2+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s21+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s17+
         s23->s18+
         s23->s20+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s25->s0+
         s25->s1+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s11+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s6+
         s26->s8+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s16+
         s26->s20+
         s26->s22+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s8+
         s27->s10+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s19+
         s27->s23+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s2+
         s28->s4+
         s28->s6+
         s28->s9+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s18+
         s28->s20+
         s28->s24+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s19+
         s29->s22+
         s29->s23+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r2+
         r8->r3+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r3+
         r10->r4+
         r11->r1+
         r11->r2+
         r11->r8+
         r11->r9+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r7+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r10+
         r18->r11+
         r18->r14+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r15+
         r19->r18+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r15+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r18+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r16+
         r22->r17+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r7+
         r23->r8+
         r23->r11+
         r23->r13+
         r23->r18+
         r23->r20+
         r24->r0+
         r24->r6+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r25->r2+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r12+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r22+
         r26->r0+
         r26->r1+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r12+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r5+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r9+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r27+
         r29->r0+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r8+
         r29->r14+
         r29->r15+
         r29->r19+
         r29->r20+
         r29->r22+
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
one sig req3 extends Request{}{
sub=s1
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r12
    m = permission
    p = 0
    c = c7+c5+c6+c8+c1+c3
}
one sig rule1 extends Rule{}{
    s =s27
    t =r14
    m = prohibition
    p = 3
    c = c5+c2+c3+c7+c9+c8
}
one sig rule2 extends Rule{}{
    s =s18
    t =r22
    m = prohibition
    p = 4
    c = c1+c3+c6+c2
}
one sig rule3 extends Rule{}{
    s =s18
    t =r26
    m = permission
    p = 0
    c = c0+c5+c4+c9+c8+c1+c3
}
one sig rule4 extends Rule{}{
    s =s18
    t =r5
    m = prohibition
    p = 2
    c = c7+c1+c9+c4+c0+c5
}
one sig rule5 extends Rule{}{
    s =s22
    t =r12
    m = permission
    p = 0
    c = c8+c7+c2+c0+c3+c6
}
one sig rule6 extends Rule{}{
    s =s5
    t =r18
    m = prohibition
    p = 0
    c = c7+c2+c4+c5
}
one sig rule7 extends Rule{}{
    s =s23
    t =r20
    m = prohibition
    p = 0
    c = c6+c9+c5+c0
}
one sig rule8 extends Rule{}{
    s =s26
    t =r9
    m = prohibition
    p = 1
    c = c3+c7+c1+c8+c4+c9
}
one sig rule9 extends Rule{}{
    s =s5
    t =r2
    m = prohibition
    p = 0
    c = c5+c9+c4
}
one sig rule10 extends Rule{}{
    s =s10
    t =r14
    m = permission
    p = 3
    c = c4+c5+c1+c2+c9+c3+c0+c8
}
one sig rule11 extends Rule{}{
    s =s22
    t =r4
    m = permission
    p = 4
    c = c6+c1
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
run accessReq3_c0{access_condition[req3,c0]} for 4
run accessReq3_c1{access_condition[req3,c1]} for 4
run accessReq3_c2{access_condition[req3,c2]} for 4
run accessReq3_c3{access_condition[req3,c3]} for 4
run accessReq3_c4{access_condition[req3,c4]} for 4
run accessReq3_c5{access_condition[req3,c5]} for 4
run accessReq3_c6{access_condition[req3,c6]} for 4
run accessReq3_c7{access_condition[req3,c7]} for 4
run accessReq3_c8{access_condition[req3,c8]} for 4
run accessReq3_c9{access_condition[req3,c9]} for 4
