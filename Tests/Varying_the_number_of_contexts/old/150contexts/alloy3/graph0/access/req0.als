module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
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
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s3+
         s6->s5+
         s7->s3+
         s7->s5+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s1+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s6+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s4+
         s12->s7+
         s12->s8+
         s13->s1+
         s13->s3+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s10+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s10+
         s16->s11+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s11+
         s18->s14+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s9+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s12+
         s20->s13+
         s20->s16+
         s20->s18+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s3+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s12+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s22+
         s24->s1+
         s24->s3+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s15+
         s24->s18+
         s24->s19+
         s24->s20+
         s25->s0+
         s25->s1+
         s25->s3+
         s25->s6+
         s25->s9+
         s25->s13+
         s25->s14+
         s25->s18+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s15+
         s26->s19+
         s26->s21+
         s26->s23+
         s26->s24+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s9+
         s27->s13+
         s27->s15+
         s27->s20+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s6+
         s28->s9+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s3+
         s29->s4+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s18+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r12->r1+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r4+
         r17->r7+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r9+
         r19->r14+
         r19->r17+
         r19->r18+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r19+
         r21->r2+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r17+
         r21->r18+
         r21->r20+
         r22->r2+
         r22->r5+
         r22->r7+
         r22->r13+
         r22->r14+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r5+
         r23->r9+
         r23->r11+
         r23->r13+
         r23->r17+
         r23->r22+
         r24->r2+
         r24->r4+
         r24->r7+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r22+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r9+
         r25->r10+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r18+
         r25->r19+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r21+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r2+
         r27->r5+
         r27->r6+
         r27->r8+
         r27->r10+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r23+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r10+
         r28->r12+
         r28->r16+
         r28->r17+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r11+
         r29->r12+
         r29->r15+
         r29->r19+
         r29->r20+
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
    s =s2
    t =r24
    m = prohibition
    p = 1
    c = c7+c4+c9+c1
}
one sig rule1 extends Rule{}{
    s =s8
    t =r29
    m = permission
    p = 4
    c = c8+c1+c7+c0
}
one sig rule2 extends Rule{}{
    s =s6
    t =r0
    m = prohibition
    p = 1
    c = c3+c2+c4+c1+c5+c6
}
one sig rule3 extends Rule{}{
    s =s29
    t =r24
    m = prohibition
    p = 0
    c = c3+c9+c8+c2+c4+c5
}
one sig rule4 extends Rule{}{
    s =s23
    t =r0
    m = permission
    p = 0
    c = c9+c2+c0+c5
}
one sig rule5 extends Rule{}{
    s =s12
    t =r0
    m = permission
    p = 4
    c = c4+c3+c8+c5
}
one sig rule6 extends Rule{}{
    s =s3
    t =r26
    m = prohibition
    p = 1
    c = c9+c1+c4+c6+c3+c8
}
one sig rule7 extends Rule{}{
    s =s8
    t =r21
    m = prohibition
    p = 2
    c = c3+c6+c4+c5
}
one sig rule8 extends Rule{}{
    s =s1
    t =r14
    m = prohibition
    p = 3
    c = c5+c4+c1+c0+c6+c9
}
one sig rule9 extends Rule{}{
    s =s11
    t =r29
    m = prohibition
    p = 0
    c = c7+c0+c2+c3+c5
}
one sig rule10 extends Rule{}{
    s =s19
    t =r12
    m = permission
    p = 0
    c = c7+c5+c3+c1+c9
}
one sig rule11 extends Rule{}{
    s =s5
    t =r28
    m = permission
    p = 4
    c = c8+c5+c6+c2
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
