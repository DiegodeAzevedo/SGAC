module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s1+
         s4->s0+
         s4->s2+
         s5->s3+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s3+
         s7->s4+
         s8->s1+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s3+
         s9->s7+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s7+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s11+
         s15->s1+
         s15->s3+
         s15->s7+
         s15->s10+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s3+
         s17->s7+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s3+
         s19->s4+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s18+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s8+
         s20->s10+
         s20->s14+
         s20->s15+
         s20->s18+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s10+
         s21->s12+
         s21->s15+
         s21->s17+
         s21->s20+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s9+
         s22->s11+
         s22->s15+
         s22->s16+
         s22->s19+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s6+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s17+
         s24->s20+
         s24->s22+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s9+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s18+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s6+
         s26->s10+
         s26->s12+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s20+
         s26->s21+
         s26->s22+
         s27->s1+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s21+
         s27->s22+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s14+
         s28->s15+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s27+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s21+
         s29->s25+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r2+
         r4->r3+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r6+
         r12->r0+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r14->r5+
         r14->r7+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r13+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r12+
         r18->r16+
         r19->r0+
         r19->r3+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r20->r1+
         r20->r3+
         r20->r5+
         r20->r9+
         r20->r10+
         r20->r13+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r8+
         r21->r9+
         r21->r15+
         r21->r16+
         r21->r17+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r14+
         r22->r16+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r3+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r9+
         r24->r10+
         r24->r13+
         r24->r18+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r26->r0+
         r26->r3+
         r26->r4+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r21+
         r26->r24+
         r27->r0+
         r27->r6+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r22+
         r27->r26+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r11+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r27+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r6+
         r29->r7+
         r29->r9+
         r29->r11+
         r29->r14+
         r29->r18+
         r29->r20+
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
    s =s1
    t =r15
    m = permission
    p = 2
    c = c9+c0
}
one sig rule1 extends Rule{}{
    s =s6
    t =r26
    m = permission
    p = 2
    c = c5+c0+c2+c9+c8+c6+c3
}
one sig rule2 extends Rule{}{
    s =s14
    t =r18
    m = permission
    p = 2
    c = c1+c3
}
one sig rule3 extends Rule{}{
    s =s15
    t =r6
    m = prohibition
    p = 3
    c = c5+c0
}
one sig rule4 extends Rule{}{
    s =s23
    t =r28
    m = prohibition
    p = 2
    c = c5
}
one sig rule5 extends Rule{}{
    s =s4
    t =r23
    m = prohibition
    p = 2
    c = c3+c9+c0+c1+c8
}
one sig rule6 extends Rule{}{
    s =s9
    t =r2
    m = prohibition
    p = 2
    c = c5+c9
}
one sig rule7 extends Rule{}{
    s =s14
    t =r18
    m = prohibition
    p = 1
    c = c0+c1+c7+c8+c9
}
one sig rule8 extends Rule{}{
    s =s14
    t =r11
    m = prohibition
    p = 1
    c = c1+c3+c8+c7
}
one sig rule9 extends Rule{}{
    s =s18
    t =r7
    m = prohibition
    p = 0
    c = c6+c4+c1
}
one sig rule10 extends Rule{}{
    s =s21
    t =r13
    m = permission
    p = 1
    c = c7
}
one sig rule11 extends Rule{}{
    s =s6
    t =r26
    m = prohibition
    p = 4
    c = c6+c5
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
