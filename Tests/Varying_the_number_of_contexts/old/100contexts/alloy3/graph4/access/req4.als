module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s5+
         s8->s7+
         s9->s1+
         s9->s4+
         s9->s8+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s12+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s12+
         s14->s13+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s10+
         s16->s12+
         s16->s14+
         s17->s4+
         s17->s8+
         s17->s10+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s3+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s18+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s13+
         s20->s15+
         s20->s19+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s11+
         s22->s12+
         s22->s14+
         s22->s16+
         s22->s18+
         s22->s19+
         s23->s0+
         s23->s5+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s16+
         s23->s17+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s8+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s23+
         s25->s1+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s12+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s23+
         s25->s24+
         s26->s1+
         s26->s3+
         s26->s6+
         s26->s7+
         s26->s14+
         s26->s15+
         s26->s18+
         s26->s19+
         s26->s23+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s18+
         s27->s19+
         s27->s21+
         s27->s23+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s3+
         s28->s6+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s18+
         s28->s20+
         s28->s23+
         s28->s24+
         s28->s27+
         s29->s0+
         s29->s3+
         s29->s4+
         s29->s8+
         s29->s9+
         s29->s12+
         s29->s13+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s25+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r3->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r4+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r1+
         r11->r3+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r11+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r13+
         r16->r2+
         r16->r5+
         r16->r9+
         r16->r11+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r12+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r5+
         r20->r8+
         r20->r9+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r13+
         r21->r16+
         r21->r20+
         r22->r1+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r9+
         r22->r15+
         r22->r16+
         r22->r19+
         r23->r0+
         r23->r2+
         r23->r4+
         r23->r6+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r17+
         r23->r20+
         r23->r21+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r17+
         r24->r19+
         r24->r21+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r15+
         r25->r16+
         r25->r21+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r7+
         r26->r10+
         r26->r12+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r22+
         r26->r25+
         r27->r0+
         r27->r3+
         r27->r9+
         r27->r11+
         r27->r15+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r8+
         r28->r9+
         r28->r11+
         r28->r15+
         r28->r16+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r9+
         r29->r10+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r24+
         r29->r25+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 1
    c = c4+c5+c1+c7+c9
}
one sig rule1 extends Rule{}{
    s =s6
    t =r10
    m = prohibition
    p = 4
    c = c9+c1+c0+c4+c7
}
one sig rule2 extends Rule{}{
    s =s6
    t =r28
    m = permission
    p = 1
    c = c4
}
one sig rule3 extends Rule{}{
    s =s18
    t =r23
    m = permission
    p = 2
    c = c5+c2+c0+c4+c1+c6
}
one sig rule4 extends Rule{}{
    s =s15
    t =r26
    m = permission
    p = 1
    c = c2+c3+c1+c0
}
one sig rule5 extends Rule{}{
    s =s7
    t =r15
    m = permission
    p = 0
    c = c5+c2+c0+c9+c4
}
one sig rule6 extends Rule{}{
    s =s2
    t =r23
    m = prohibition
    p = 1
    c = c3+c7+c4+c1+c5+c9
}
one sig rule7 extends Rule{}{
    s =s12
    t =r24
    m = prohibition
    p = 3
    c = c4+c1+c0+c2+c8+c3
}
one sig rule8 extends Rule{}{
    s =s8
    t =r16
    m = permission
    p = 0
    c = c3+c7+c8+c6+c1
}
one sig rule9 extends Rule{}{
    s =s16
    t =r9
    m = permission
    p = 0
    c = c3+c6+c1+c9+c4
}
one sig rule10 extends Rule{}{
    s =s5
    t =r9
    m = permission
    p = 2
    c = c8+c3+c6+c9
}
one sig rule11 extends Rule{}{
    s =s3
    t =r22
    m = permission
    p = 1
    c = c9+c3+c7+c8
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
run accessReq4_c0{access_condition[req4,c0]} for 4
run accessReq4_c1{access_condition[req4,c1]} for 4
run accessReq4_c2{access_condition[req4,c2]} for 4
run accessReq4_c3{access_condition[req4,c3]} for 4
run accessReq4_c4{access_condition[req4,c4]} for 4
run accessReq4_c5{access_condition[req4,c5]} for 4
run accessReq4_c6{access_condition[req4,c6]} for 4
run accessReq4_c7{access_condition[req4,c7]} for 4
run accessReq4_c8{access_condition[req4,c8]} for 4
run accessReq4_c9{access_condition[req4,c9]} for 4
