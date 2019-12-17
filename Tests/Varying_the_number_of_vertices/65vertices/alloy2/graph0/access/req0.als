module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s5->s0+
         s5->s2+
         s5->s4+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s4+
         s8->s3+
         s8->s7+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s3+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s11+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s10+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s1+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s15+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s16+
         s21->s0+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s17+
         s21->s19+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s13+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s4+
         s24->s6+
         s24->s8+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s17+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s7+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s15+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s1+
         s26->s4+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s21+
         s26->s22+
         s27->s3+
         s27->s4+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s12+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s3+
         s28->s5+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s7+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s21+
         s29->s26+
         s30->s8+
         s30->s9+
         s30->s13+
         s30->s15+
         s30->s16+
         s30->s17+
         s30->s18+
         s30->s20+
         s30->s21+
         s30->s22+
         s30->s27+
         s30->s28+
         s30->s29+
         s31->s3+
         s31->s7+
         s31->s11+
         s31->s14+
         s31->s16+
         s31->s22+
         s31->s23+
         s31->s28+
         s32->s2+
         s32->s5+
         s32->s6+
         s32->s7+
         s32->s8+
         s32->s9+
         s32->s11+
         s32->s15+
         s32->s16+
         s32->s17+
         s32->s20+
         s32->s24+
         s32->s25+
         s32->s31}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r5+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r6+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r13+
         r15->r1+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r10+
         r16->r2+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r8+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r17+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r6+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r6+
         r21->r7+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r4+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r6+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r6+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r18+
         r24->r20+
         r24->r21+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r21+
         r26->r22+
         r26->r24+
         r27->r0+
         r27->r3+
         r27->r4+
         r27->r6+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r2+
         r28->r5+
         r28->r7+
         r28->r11+
         r28->r12+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r26+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r8+
         r29->r14+
         r29->r15+
         r29->r21+
         r29->r23+
         r29->r25+
         r29->r26+
         r29->r27+
         r30->r1+
         r30->r2+
         r30->r4+
         r30->r9+
         r30->r11+
         r30->r14+
         r30->r16+
         r30->r19+
         r30->r20+
         r30->r21+
         r30->r23+
         r30->r24+
         r30->r25+
         r30->r28+
         r30->r29+
         r31->r0+
         r31->r2+
         r31->r3+
         r31->r4+
         r31->r5+
         r31->r6+
         r31->r7+
         r31->r8+
         r31->r11+
         r31->r12+
         r31->r16+
         r31->r17+
         r31->r20+
         r31->r21+
         r31->r22+
         r31->r24+
         r31->r25+
         r31->r26+
         r31->r27+
         r31->r28+
         r31->r29}

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
    s =s21
    t =r10
    m = prohibition
    p = 2
    c = c2+c0+c5+c8
}
one sig rule1 extends Rule{}{
    s =s5
    t =r27
    m = prohibition
    p = 4
    c = c2+c6+c1+c3
}
one sig rule2 extends Rule{}{
    s =s4
    t =r1
    m = prohibition
    p = 0
    c = c3+c9+c4+c6+c8
}
one sig rule3 extends Rule{}{
    s =s30
    t =r15
    m = prohibition
    p = 2
    c = c9+c0+c6+c2+c4+c8+c3+c1
}
one sig rule4 extends Rule{}{
    s =s25
    t =r11
    m = permission
    p = 1
    c = c6+c1+c3+c7+c2+c0+c5+c8
}
one sig rule5 extends Rule{}{
    s =s23
    t =r25
    m = permission
    p = 1
    c = c7+c9+c4+c8+c1+c3
}
one sig rule6 extends Rule{}{
    s =s9
    t =r6
    m = prohibition
    p = 4
    c = c5+c9+c4
}
one sig rule7 extends Rule{}{
    s =s16
    t =r22
    m = permission
    p = 1
    c = c3+c8+c4
}
one sig rule8 extends Rule{}{
    s =s0
    t =r16
    m = permission
    p = 3
    c = c8+c2+c0+c5+c7+c4+c9+c1
}
one sig rule9 extends Rule{}{
    s =s26
    t =r5
    m = prohibition
    p = 0
    c = c9+c8+c1+c5+c4+c7
}
one sig rule10 extends Rule{}{
    s =s32
    t =r3
    m = prohibition
    p = 4
    c = c1+c9+c3+c8
}
one sig rule11 extends Rule{}{
    s =s3
    t =r5
    m = permission
    p = 2
    c = c8+c7
}
one sig rule12 extends Rule{}{
    s =s6
    t =r19
    m = prohibition
    p = 1
    c = c3+c4+c2+c1+c5
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
