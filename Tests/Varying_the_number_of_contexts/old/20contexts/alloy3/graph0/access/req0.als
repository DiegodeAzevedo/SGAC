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
         s3->s2+
         s4->s0+
         s4->s2+
         s5->s1+
         s5->s4+
         s6->s1+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s5+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s7+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s8+
         s14->s11+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s9+
         s15->s10+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s12+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s4+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s6+
         s20->s10+
         s20->s11+
         s20->s15+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s6+
         s21->s7+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s17+
         s22->s0+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s18+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s19+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s4+
         s24->s5+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s20+
         s24->s22+
         s25->s2+
         s25->s4+
         s25->s6+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s20+
         s25->s23+
         s26->s0+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s13+
         s26->s14+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s11+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s26+
         s28->s2+
         s28->s5+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s4+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s12+
         s29->s16+
         s29->s18+
         s29->s20+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r3+
         r8->r1+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r4+
         r10->r8+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r5+
         r13->r7+
         r13->r9+
         r13->r10+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r15+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r3+
         r20->r5+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r8+
         r22->r11+
         r22->r16+
         r22->r17+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r3+
         r23->r5+
         r23->r12+
         r23->r13+
         r23->r15+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r17+
         r24->r18+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r4+
         r25->r5+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r15+
         r25->r20+
         r25->r24+
         r26->r0+
         r26->r3+
         r26->r6+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r5+
         r27->r10+
         r27->r11+
         r27->r14+
         r27->r16+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r25+
         r28->r0+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r8+
         r28->r11+
         r28->r13+
         r28->r18+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r2+
         r29->r6+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r22+
         r29->r23+
         r29->r24+
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
    s =s4
    t =r1
    m = prohibition
    p = 3
    c = c3+c7+c6+c9+c2
}
one sig rule1 extends Rule{}{
    s =s10
    t =r29
    m = permission
    p = 3
    c = c3+c0
}
one sig rule2 extends Rule{}{
    s =s9
    t =r11
    m = permission
    p = 4
    c = c6+c3+c0+c2
}
one sig rule3 extends Rule{}{
    s =s15
    t =r22
    m = prohibition
    p = 0
    c = c0+c2+c1+c5
}
one sig rule4 extends Rule{}{
    s =s9
    t =r2
    m = permission
    p = 0
    c = c3+c4+c7+c0+c8+c5+c9
}
one sig rule5 extends Rule{}{
    s =s16
    t =r28
    m = permission
    p = 3
    c = c6+c0+c2+c9+c7
}
one sig rule6 extends Rule{}{
    s =s16
    t =r7
    m = prohibition
    p = 4
    c = c3+c0
}
one sig rule7 extends Rule{}{
    s =s14
    t =r6
    m = permission
    p = 3
    c = c5
}
one sig rule8 extends Rule{}{
    s =s2
    t =r22
    m = permission
    p = 1
    c = c0+c3+c9
}
one sig rule9 extends Rule{}{
    s =s13
    t =r18
    m = permission
    p = 1
    c = c5+c2+c0
}
one sig rule10 extends Rule{}{
    s =s19
    t =r6
    m = prohibition
    p = 4
    c = c9+c1+c7+c4+c5
}
one sig rule11 extends Rule{}{
    s =s10
    t =r23
    m = prohibition
    p = 0
    c = c4+c7+c9+c8+c3
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
