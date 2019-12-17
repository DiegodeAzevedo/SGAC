module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s5+
         s10->s6+
         s11->s0+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s6+
         s14->s9+
         s15->s4+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s8+
         s20->s11+
         s20->s14+
         s20->s17+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s12+
         s21->s13+
         s21->s15+
         s21->s18+
         s21->s19+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s6+
         s22->s8+
         s22->s10+
         s22->s14+
         s22->s18+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s12+
         s23->s16+
         s23->s17+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s25->s1+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s8+
         s25->s11+
         s25->s14+
         s25->s15+
         s25->s18+
         s25->s19+
         s25->s22+
         s25->s24+
         s26->s2+
         s26->s3+
         s26->s7+
         s26->s11+
         s26->s12+
         s26->s15+
         s26->s16+
         s26->s18+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s20+
         s27->s21+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s2+
         s28->s5+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s17+
         s28->s19+
         s28->s20+
         s28->s23+
         s28->s24+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s5+
         s29->s10+
         s29->s13+
         s29->s15+
         s29->s22+
         s29->s24+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r0+
         r5->r2+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r7+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r10+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r14->r2+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r7+
         r15->r8+
         r15->r13+
         r16->r0+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r7+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r17+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r7+
         r20->r12+
         r20->r14+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r3+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r8+
         r22->r17+
         r22->r19+
         r23->r1+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r22+
         r24->r3+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r15+
         r24->r19+
         r24->r21+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r13+
         r25->r14+
         r25->r17+
         r25->r20+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r10+
         r26->r11+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r20+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r5+
         r27->r6+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r15+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r4+
         r28->r7+
         r28->r8+
         r28->r10+
         r28->r13+
         r28->r18+
         r28->r20+
         r28->r21+
         r28->r24+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r7+
         r29->r11+
         r29->r15+
         r29->r20+
         r29->r23+
         r29->r24+
         r29->r26+
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
    s =s26
    t =r12
    m = prohibition
    p = 1
    c = c3+c9+c8
}
one sig rule1 extends Rule{}{
    s =s19
    t =r19
    m = prohibition
    p = 3
    c = c2+c3+c7+c8+c0+c5
}
one sig rule2 extends Rule{}{
    s =s2
    t =r23
    m = permission
    p = 3
    c = c9+c3+c6+c1
}
one sig rule3 extends Rule{}{
    s =s11
    t =r6
    m = prohibition
    p = 1
    c = c2+c9
}
one sig rule4 extends Rule{}{
    s =s6
    t =r12
    m = prohibition
    p = 0
    c = c2+c8
}
one sig rule5 extends Rule{}{
    s =s28
    t =r22
    m = prohibition
    p = 1
    c = c7
}
one sig rule6 extends Rule{}{
    s =s12
    t =r28
    m = prohibition
    p = 1
    c = c2+c4+c1+c6+c3+c7+c9
}
one sig rule7 extends Rule{}{
    s =s2
    t =r26
    m = prohibition
    p = 4
    c = c0+c4+c8+c6+c5
}
one sig rule8 extends Rule{}{
    s =s19
    t =r21
    m = prohibition
    p = 1
    c = c7+c6+c5
}
one sig rule9 extends Rule{}{
    s =s14
    t =r23
    m = prohibition
    p = 4
    c = c8+c4+c9+c6+c5+c7+c2
}
one sig rule10 extends Rule{}{
    s =s27
    t =r6
    m = prohibition
    p = 2
    c = c7+c5+c2
}
one sig rule11 extends Rule{}{
    s =s6
    t =r29
    m = permission
    p = 0
    c = c8
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
