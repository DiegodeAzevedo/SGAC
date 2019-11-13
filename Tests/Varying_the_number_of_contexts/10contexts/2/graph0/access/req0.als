module filepath/param/graph/property/req
open filepath/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s7+
         s11->s8+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s9+
         s12->s10+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s7+
         s13->s9+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s12+
         s14->s13+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s6+
         s17->s7+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s16+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s15+
         s21->s17+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s9+
         s22->s13+
         s22->s18+
         s22->s19+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s4+
         s24->s12+
         s24->s16+
         s24->s22+
         s25->s2+
         s25->s3+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s10+
         s25->s13+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s4+
         s26->s6+
         s26->s13+
         s26->s14+
         s26->s19+
         s26->s20+
         s26->s22+
         s26->s23+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s15+
         s27->s16+
         s27->s22+
         s27->s24+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s8+
         s28->s11+
         s28->s12+
         s28->s18+
         s28->s20+
         s28->s21+
         s28->s23+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s6+
         s29->s8+
         s29->s9+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
subSucc=r2->r0+
         r2->r1+
         r3->r1+
         r4->r2+
         r5->r2+
         r5->r4+
         r6->r3+
         r6->r5+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r4+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r7+
         r13->r8+
         r13->r11+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r11+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r4+
         r18->r5+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r4+
         r20->r6+
         r20->r14+
         r20->r15+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r5+
         r21->r6+
         r21->r9+
         r21->r12+
         r21->r16+
         r21->r19+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r17+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r4+
         r24->r7+
         r24->r9+
         r24->r12+
         r24->r14+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r11+
         r25->r13+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r10+
         r26->r11+
         r26->r17+
         r26->r18+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r6+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r19+
         r27->r22+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r14+
         r28->r15+
         r28->r17+
         r28->r19+
         r28->r24+
         r28->r27+
         r29->r0+
         r29->r5+
         r29->r6+
         r29->r9+
         r29->r12+
         r29->r16+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r26+
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
    s =s12
    t =r28
    m = prohibition
    p = 1
    c = c5+c6+c9+c0+c2
}
one sig rule1 extends Rule{}{
    s =s29
    t =r14
    m = permission
    p = 1
    c = c7+c8+c5+c3+c1+c2
}
one sig rule2 extends Rule{}{
    s =s23
    t =r0
    m = permission
    p = 4
    c = c4+c7+c1+c5
}
one sig rule3 extends Rule{}{
    s =s26
    t =r19
    m = permission
    p = 3
    c = c6+c2+c1+c9+c7+c8
}
one sig rule4 extends Rule{}{
    s =s22
    t =r20
    m = prohibition
    p = 4
    c = c0+c3
}
one sig rule5 extends Rule{}{
    s =s0
    t =r17
    m = permission
    p = 2
    c = c9+c1
}
one sig rule6 extends Rule{}{
    s =s22
    t =r10
    m = permission
    p = 1
    c = c9+c4+c0
}
one sig rule7 extends Rule{}{
    s =s9
    t =r25
    m = permission
    p = 3
    c = c2
}
one sig rule8 extends Rule{}{
    s =s14
    t =r5
    m = permission
    p = 4
    c = c0+c7+c3+c4
}
one sig rule9 extends Rule{}{
    s =s23
    t =r0
    m = prohibition
    p = 3
    c = c7+c5+c0+c6+c8+c4
}
one sig rule10 extends Rule{}{
    s =s18
    t =r7
    m = prohibition
    p = 0
    c = c8+c1+c5+c7+c4+c2+c3
}
one sig rule11 extends Rule{}{
    s =s22
    t =r0
    m = permission
    p = 2
    c = c2+c9+c8+c4
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
run accessReq0_c5{access_access_condition[req0,c5]} for 4
run accessReq0_c6{access_access_condition[req0,c6]} for 4
run accessReq0_c9{access_access_condition[req0,c9]} for 4
run accessReq0_c0{access_access_condition[req0,c0]} for 4
run accessReq0_c2{access_access_condition[req0,c2]} for 4
run accessReq0_c7{access_access_condition[req0,c7]} for 4
run accessReq0_c8{access_access_condition[req0,c8]} for 4
run accessReq0_c5{access_access_condition[req0,c5]} for 4
run accessReq0_c3{access_access_condition[req0,c3]} for 4
run accessReq0_c1{access_access_condition[req0,c1]} for 4
run accessReq0_c2{access_access_condition[req0,c2]} for 4
run accessReq0_c4{access_access_condition[req0,c4]} for 4
run accessReq0_c7{access_access_condition[req0,c7]} for 4
run accessReq0_c1{access_access_condition[req0,c1]} for 4
run accessReq0_c5{access_access_condition[req0,c5]} for 4
run accessReq0_c6{access_access_condition[req0,c6]} for 4
run accessReq0_c2{access_access_condition[req0,c2]} for 4
run accessReq0_c1{access_access_condition[req0,c1]} for 4
run accessReq0_c9{access_access_condition[req0,c9]} for 4
run accessReq0_c7{access_access_condition[req0,c7]} for 4
run accessReq0_c8{access_access_condition[req0,c8]} for 4
run accessReq0_c0{access_access_condition[req0,c0]} for 4
run accessReq0_c3{access_access_condition[req0,c3]} for 4
run accessReq0_c9{access_access_condition[req0,c9]} for 4
run accessReq0_c1{access_access_condition[req0,c1]} for 4
run accessReq0_c9{access_access_condition[req0,c9]} for 4
run accessReq0_c4{access_access_condition[req0,c4]} for 4
run accessReq0_c0{access_access_condition[req0,c0]} for 4
run accessReq0_c2{access_access_condition[req0,c2]} for 4
run accessReq0_c0{access_access_condition[req0,c0]} for 4
run accessReq0_c7{access_access_condition[req0,c7]} for 4
run accessReq0_c3{access_access_condition[req0,c3]} for 4
run accessReq0_c4{access_access_condition[req0,c4]} for 4
run accessReq0_c7{access_access_condition[req0,c7]} for 4
run accessReq0_c5{access_access_condition[req0,c5]} for 4
run accessReq0_c0{access_access_condition[req0,c0]} for 4
run accessReq0_c6{access_access_condition[req0,c6]} for 4
run accessReq0_c8{access_access_condition[req0,c8]} for 4
run accessReq0_c4{access_access_condition[req0,c4]} for 4
run accessReq0_c8{access_access_condition[req0,c8]} for 4
run accessReq0_c1{access_access_condition[req0,c1]} for 4
run accessReq0_c5{access_access_condition[req0,c5]} for 4
run accessReq0_c7{access_access_condition[req0,c7]} for 4
run accessReq0_c4{access_access_condition[req0,c4]} for 4
run accessReq0_c2{access_access_condition[req0,c2]} for 4
run accessReq0_c3{access_access_condition[req0,c3]} for 4
run accessReq0_c2{access_access_condition[req0,c2]} for 4
run accessReq0_c9{access_access_condition[req0,c9]} for 4
run accessReq0_c8{access_access_condition[req0,c8]} for 4
run accessReq0_c4{access_access_condition[req0,c4]} for 4
