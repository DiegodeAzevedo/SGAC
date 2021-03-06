module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s3+
         s6->s0+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s8+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s11+
         s14->s3+
         s14->s8+
         s14->s10+
         s14->s11+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s11+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s13+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s7+
         s18->s9+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s13+
         s19->s15+
         s19->s17+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s17+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s14+
         s22->s15+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s8+
         s24->s11+
         s24->s12+
         s24->s14+
         s24->s16+
         s24->s20+
         s24->s23+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s7+
         s25->s10+
         s25->s11+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s2+
         s26->s7+
         s26->s9+
         s26->s13+
         s26->s15+
         s26->s17+
         s26->s21+
         s26->s23+
         s26->s24+
         s27->s1+
         s27->s6+
         s27->s7+
         s27->s9+
         s27->s12+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s23+
         s27->s24+
         s28->s0+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s7+
         s28->s9+
         s28->s11+
         s28->s13+
         s28->s14+
         s28->s18+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s12+
         s29->s13+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s21+
         s29->s22+
         s29->s24+
         s29->s25+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r6+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r5+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r10+
         r14->r3+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r17->r1+
         r17->r3+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r1+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r17+
         r20->r0+
         r20->r2+
         r20->r4+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r2+
         r21->r4+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r16+
         r22->r0+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r16+
         r22->r17+
         r22->r19+
         r22->r20+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r20+
         r23->r21+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r10+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r22+
         r24->r23+
         r25->r4+
         r25->r10+
         r25->r12+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r4+
         r26->r7+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r13+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r26+
         r28->r0+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r9+
         r28->r11+
         r28->r14+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r24+
         r29->r0+
         r29->r3+
         r29->r7+
         r29->r12+
         r29->r14+
         r29->r20+
         r29->r21+
         r29->r23+
         r29->r25}

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
    s =s15
    t =r7
    m = permission
    p = 2
    c = c0+c9+c8
}
one sig rule1 extends Rule{}{
    s =s19
    t =r14
    m = prohibition
    p = 4
    c = c1+c4
}
one sig rule2 extends Rule{}{
    s =s13
    t =r16
    m = prohibition
    p = 2
    c = c1+c5+c9+c4
}
one sig rule3 extends Rule{}{
    s =s7
    t =r28
    m = permission
    p = 4
    c = c5+c4+c8+c1+c7
}
one sig rule4 extends Rule{}{
    s =s12
    t =r20
    m = prohibition
    p = 2
    c = c4+c9
}
one sig rule5 extends Rule{}{
    s =s1
    t =r22
    m = permission
    p = 2
    c = c8+c3+c4+c0+c7+c6
}
one sig rule6 extends Rule{}{
    s =s13
    t =r12
    m = permission
    p = 1
    c = c0+c2+c6+c5+c9+c1
}
one sig rule7 extends Rule{}{
    s =s13
    t =r7
    m = prohibition
    p = 4
    c = c9+c3+c4+c5+c2
}
one sig rule8 extends Rule{}{
    s =s21
    t =r21
    m = permission
    p = 1
    c = c7+c4
}
one sig rule9 extends Rule{}{
    s =s17
    t =r3
    m = permission
    p = 3
    c = c6+c4+c3+c1+c9
}
one sig rule10 extends Rule{}{
    s =s11
    t =r16
    m = permission
    p = 2
    c = c2+c4+c3+c0+c5+c7+c9
}
one sig rule11 extends Rule{}{
    s =s18
    t =r25
    m = permission
    p = 4
    c = c9+c6+c8+c4+c2
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
