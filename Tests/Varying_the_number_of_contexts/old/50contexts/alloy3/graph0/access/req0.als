module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s4+
         s8->s5+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s9+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s11+
         s14->s12+
         s15->s2+
         s15->s4+
         s15->s7+
         s15->s10+
         s15->s12+
         s16->s4+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s4+
         s17->s8+
         s17->s9+
         s17->s12+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s3+
         s19->s6+
         s19->s9+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s6+
         s20->s8+
         s20->s10+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s3+
         s21->s4+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s14+
         s21->s16+
         s21->s17+
         s22->s0+
         s22->s3+
         s22->s5+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s21+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s12+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s21+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s4+
         s26->s7+
         s26->s9+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s23+
         s27->s0+
         s27->s5+
         s27->s7+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s21+
         s27->s23+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s18+
         s28->s22+
         s28->s26+
         s28->s27+
         s29->s1+
         s29->s3+
         s29->s7+
         s29->s11+
         s29->s16+
         s29->s19+
         s29->s20+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r6+
         r11->r0+
         r11->r4+
         r11->r5+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r10+
         r14->r0+
         r14->r2+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r3+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r13+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r12+
         r20->r14+
         r20->r16+
         r20->r19+
         r21->r0+
         r21->r3+
         r21->r6+
         r21->r10+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r22->r2+
         r22->r5+
         r22->r10+
         r22->r13+
         r22->r14+
         r22->r17+
         r22->r19+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r7+
         r23->r10+
         r23->r14+
         r23->r16+
         r23->r19+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r17+
         r24->r18+
         r24->r21+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r15+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r6+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r17+
         r26->r18+
         r26->r21+
         r27->r0+
         r27->r4+
         r27->r5+
         r27->r7+
         r27->r8+
         r27->r13+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r5+
         r28->r7+
         r28->r11+
         r28->r14+
         r28->r16+
         r28->r19+
         r28->r20+
         r29->r0+
         r29->r7+
         r29->r11+
         r29->r12+
         r29->r14+
         r29->r16+
         r29->r21+
         r29->r23+
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
    s =s3
    t =r21
    m = permission
    p = 4
    c = c6+c4
}
one sig rule1 extends Rule{}{
    s =s3
    t =r21
    m = prohibition
    p = 2
    c = c6+c2+c5+c7
}
one sig rule2 extends Rule{}{
    s =s15
    t =r28
    m = permission
    p = 0
    c = c8+c0+c7+c4+c6+c5
}
one sig rule3 extends Rule{}{
    s =s13
    t =r23
    m = permission
    p = 1
    c = c1+c9+c0+c4+c3+c6
}
one sig rule4 extends Rule{}{
    s =s23
    t =r25
    m = prohibition
    p = 3
    c = c3+c8+c4+c7+c0
}
one sig rule5 extends Rule{}{
    s =s11
    t =r12
    m = prohibition
    p = 4
    c = c9+c2+c5+c4+c7+c3
}
one sig rule6 extends Rule{}{
    s =s2
    t =r7
    m = prohibition
    p = 3
    c = c5+c0+c1
}
one sig rule7 extends Rule{}{
    s =s19
    t =r27
    m = prohibition
    p = 4
    c = c9+c2+c6+c8
}
one sig rule8 extends Rule{}{
    s =s0
    t =r6
    m = prohibition
    p = 0
    c = c4+c2+c5+c0+c9+c1
}
one sig rule9 extends Rule{}{
    s =s20
    t =r29
    m = prohibition
    p = 1
    c = c5+c8+c7+c2+c4+c1+c3+c9
}
one sig rule10 extends Rule{}{
    s =s26
    t =r7
    m = prohibition
    p = 1
    c = c0+c1+c4+c2+c9+c5
}
one sig rule11 extends Rule{}{
    s =s18
    t =r0
    m = permission
    p = 3
    c = c5+c1+c2+c8
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
