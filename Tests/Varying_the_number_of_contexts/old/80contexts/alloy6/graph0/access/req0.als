module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s1+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s9+
         s12->s11+
         s13->s1+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s7+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s15+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s9+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s14+
         s19->s16+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s5+
         s21->s8+
         s21->s10+
         s21->s13+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s20+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s15+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s9+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s23+
         s25->s0+
         s25->s4+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s17+
         s25->s19+
         s25->s22+
         s26->s0+
         s26->s3+
         s26->s5+
         s26->s8+
         s26->s9+
         s26->s12+
         s26->s13+
         s26->s24+
         s26->s25+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s17+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s3+
         s28->s10+
         s28->s11+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s3+
         s29->s4+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r3+
         r6->r1+
         r7->r1+
         r7->r2+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r8+
         r10->r1+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r5+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r10+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r16+
         r19->r0+
         r19->r2+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r13+
         r20->r14+
         r20->r18+
         r20->r19+
         r21->r3+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r11+
         r21->r14+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r20+
         r22->r3+
         r22->r5+
         r22->r7+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r13+
         r24->r15+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r6+
         r25->r7+
         r25->r16+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r11+
         r26->r14+
         r26->r17+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r9+
         r27->r12+
         r27->r14+
         r27->r18+
         r27->r21+
         r27->r23+
         r27->r25+
         r28->r1+
         r28->r5+
         r28->r8+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r18+
         r28->r20+
         r28->r26+
         r29->r8+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r20+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r25+
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
    s =s28
    t =r5
    m = prohibition
    p = 4
    c = c6+c2+c7+c3
}
one sig rule1 extends Rule{}{
    s =s10
    t =r13
    m = prohibition
    p = 3
    c = c8+c5+c6+c9
}
one sig rule2 extends Rule{}{
    s =s11
    t =r7
    m = permission
    p = 4
    c = c6+c4
}
one sig rule3 extends Rule{}{
    s =s4
    t =r27
    m = prohibition
    p = 1
    c = c4+c8+c5+c1+c0+c9+c3
}
one sig rule4 extends Rule{}{
    s =s16
    t =r2
    m = prohibition
    p = 1
    c = c3+c6+c9
}
one sig rule5 extends Rule{}{
    s =s7
    t =r19
    m = permission
    p = 4
    c = c9+c2+c0+c5+c4+c8+c6
}
one sig rule6 extends Rule{}{
    s =s11
    t =r25
    m = prohibition
    p = 3
    c = c2+c5
}
one sig rule7 extends Rule{}{
    s =s8
    t =r24
    m = prohibition
    p = 3
    c = c1+c6+c3+c4+c5+c9
}
one sig rule8 extends Rule{}{
    s =s14
    t =r18
    m = prohibition
    p = 4
    c = c3+c1+c4
}
one sig rule9 extends Rule{}{
    s =s24
    t =r12
    m = prohibition
    p = 2
    c = c2+c9+c8+c5+c7
}
one sig rule10 extends Rule{}{
    s =s1
    t =r4
    m = permission
    p = 0
    c = c5+c6+c3+c9+c7
}
one sig rule11 extends Rule{}{
    s =s25
    t =r29
    m = prohibition
    p = 2
    c = c4
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
