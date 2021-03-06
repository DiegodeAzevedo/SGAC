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
         s4->s3+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s1+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s6+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s8+
         s18->s10+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s11+
         s19->s14+
         s19->s18+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s14+
         s20->s17+
         s20->s18+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s11+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s3+
         s22->s9+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s21+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s17+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s15+
         s24->s20+
         s24->s21+
         s24->s22+
         s25->s1+
         s25->s3+
         s25->s6+
         s25->s7+
         s25->s9+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s18+
         s25->s21+
         s25->s23+
         s26->s1+
         s26->s3+
         s26->s7+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s16+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s8+
         s27->s11+
         s27->s13+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s26+
         s28->s2+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s16+
         s28->s19+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s21+
         s29->s22+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r2+
         r6->r1+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r6+
         r10->r3+
         r10->r4+
         r10->r8+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r11+
         r14->r12+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r2+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r9+
         r18->r15+
         r18->r17+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r18+
         r20->r0+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r17+
         r21->r1+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r4+
         r22->r5+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r17+
         r22->r21+
         r23->r3+
         r23->r4+
         r23->r7+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r8+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r17+
         r24->r18+
         r24->r21+
         r24->r22+
         r25->r2+
         r25->r5+
         r25->r6+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r15+
         r26->r18+
         r26->r21+
         r26->r24+
         r26->r25+
         r27->r2+
         r27->r4+
         r27->r8+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r19+
         r27->r21+
         r27->r22+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r3+
         r28->r7+
         r28->r10+
         r28->r12+
         r28->r14+
         r28->r17+
         r28->r19+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r2+
         r29->r5+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r18+
         r29->r19+
         r29->r23+
         r29->r24+
         r29->r25+
         r29->r27}

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
    s =s5
    t =r5
    m = permission
    p = 4
    c = c6+c2+c8+c0+c3+c5
}
one sig rule1 extends Rule{}{
    s =s17
    t =r23
    m = prohibition
    p = 1
    c = c6+c8
}
one sig rule2 extends Rule{}{
    s =s21
    t =r18
    m = prohibition
    p = 3
    c = c6+c1
}
one sig rule3 extends Rule{}{
    s =s15
    t =r19
    m = prohibition
    p = 4
    c = c4+c3+c8
}
one sig rule4 extends Rule{}{
    s =s2
    t =r23
    m = permission
    p = 2
    c = c3
}
one sig rule5 extends Rule{}{
    s =s11
    t =r5
    m = prohibition
    p = 4
    c = c8+c9
}
one sig rule6 extends Rule{}{
    s =s28
    t =r14
    m = prohibition
    p = 1
    c = c8+c7+c2
}
one sig rule7 extends Rule{}{
    s =s1
    t =r8
    m = prohibition
    p = 3
    c = c7+c0+c4+c5+c6+c9+c8
}
one sig rule8 extends Rule{}{
    s =s2
    t =r24
    m = prohibition
    p = 2
    c = c4+c0
}
one sig rule9 extends Rule{}{
    s =s16
    t =r14
    m = prohibition
    p = 3
    c = c5+c0+c1
}
one sig rule10 extends Rule{}{
    s =s14
    t =r27
    m = prohibition
    p = 4
    c = c9+c4
}
one sig rule11 extends Rule{}{
    s =s29
    t =r12
    m = permission
    p = 2
    c = c0+c8+c3
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
