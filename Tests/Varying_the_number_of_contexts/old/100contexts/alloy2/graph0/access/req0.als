module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s2+
         s4->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s0+
         s7->s1+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s6+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s6+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s14+
         s18->s17+
         s19->s5+
         s19->s10+
         s19->s12+
         s19->s14+
         s19->s16+
         s19->s18+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s12+
         s20->s13+
         s20->s17+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s16+
         s22->s20+
         s23->s0+
         s23->s2+
         s23->s3+
         s23->s8+
         s23->s10+
         s23->s18+
         s23->s21+
         s23->s22+
         s24->s3+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s10+
         s24->s11+
         s24->s14+
         s24->s16+
         s24->s20+
         s24->s21+
         s24->s22+
         s25->s3+
         s25->s5+
         s25->s7+
         s25->s9+
         s25->s10+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s20+
         s25->s22+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s12+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s21+
         s26->s23+
         s27->s0+
         s27->s1+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s12+
         s27->s17+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s2+
         s28->s6+
         s28->s7+
         s28->s11+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s18+
         s28->s20+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s3+
         s29->s5+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s25+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r2+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r15->r1+
         r15->r2+
         r15->r8+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r12+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r15+
         r18->r5+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r17+
         r20->r18+
         r21->r1+
         r21->r3+
         r21->r7+
         r21->r9+
         r21->r13+
         r21->r14+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r19+
         r23->r1+
         r23->r4+
         r23->r5+
         r23->r8+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r15+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r17+
         r24->r22+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r22+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r5+
         r26->r7+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r15+
         r26->r21+
         r26->r25+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r14+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r25+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r11+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r7+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r25+
         r29->r26}

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
    s =s11
    t =r28
    m = permission
    p = 2
    c = c6+c5+c4+c0+c9+c2
}
one sig rule1 extends Rule{}{
    s =s17
    t =r15
    m = permission
    p = 0
    c = c6+c7+c2+c9
}
one sig rule2 extends Rule{}{
    s =s20
    t =r10
    m = prohibition
    p = 0
    c = c0+c2
}
one sig rule3 extends Rule{}{
    s =s25
    t =r19
    m = prohibition
    p = 1
    c = c2+c1+c4+c8
}
one sig rule4 extends Rule{}{
    s =s12
    t =r16
    m = prohibition
    p = 2
    c = c6+c7+c1+c2+c3+c9
}
one sig rule5 extends Rule{}{
    s =s18
    t =r9
    m = prohibition
    p = 0
    c = c6+c8+c0+c4+c3+c1
}
one sig rule6 extends Rule{}{
    s =s19
    t =r8
    m = permission
    p = 0
    c = c8+c4+c6+c7
}
one sig rule7 extends Rule{}{
    s =s2
    t =r28
    m = permission
    p = 1
    c = c3+c7
}
one sig rule8 extends Rule{}{
    s =s21
    t =r4
    m = prohibition
    p = 4
    c = c3
}
one sig rule9 extends Rule{}{
    s =s10
    t =r18
    m = prohibition
    p = 2
    c = c5+c9+c7+c3+c6
}
one sig rule10 extends Rule{}{
    s =s23
    t =r20
    m = prohibition
    p = 1
    c = c2+c3+c9+c7
}
one sig rule11 extends Rule{}{
    s =s16
    t =r9
    m = prohibition
    p = 2
    c = c3+c4+c0+c5+c1+c6
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
