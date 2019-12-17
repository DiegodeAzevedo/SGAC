module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s3+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s10+
         s12->s11+
         s13->s3+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s4+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s5+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s8+
         s16->s9+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s5+
         s17->s7+
         s17->s15+
         s17->s16+
         s18->s5+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s3+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s17+
         s19->s18+
         s20->s2+
         s20->s5+
         s20->s10+
         s20->s13+
         s20->s15+
         s20->s16+
         s20->s19+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s15+
         s21->s18+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s4+
         s22->s7+
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
         s23->s1+
         s23->s3+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s24->s0+
         s24->s1+
         s24->s4+
         s24->s6+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s1+
         s26->s3+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s17+
         s26->s24+
         s27->s0+
         s27->s2+
         s27->s6+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s20+
         s27->s22+
         s27->s25+
         s28->s0+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s16+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s25+
         s29->s1+
         s29->s2+
         s29->s5+
         s29->s7+
         s29->s9+
         s29->s12+
         s29->s13+
         s29->s16+
         s29->s17+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r5+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r15->r2+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r9+
         r15->r14+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r4+
         r19->r6+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r17+
         r20->r19+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r7+
         r21->r11+
         r21->r16+
         r21->r18+
         r21->r19+
         r22->r1+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r18+
         r22->r21+
         r23->r3+
         r23->r5+
         r23->r8+
         r23->r10+
         r23->r12+
         r23->r14+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r4+
         r24->r6+
         r24->r10+
         r24->r12+
         r24->r19+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r3+
         r25->r5+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r13+
         r25->r15+
         r25->r21+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r8+
         r26->r11+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r2+
         r27->r3+
         r27->r5+
         r27->r8+
         r27->r12+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r18+
         r27->r21+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r17+
         r28->r23+
         r28->r24+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r3+
         r29->r6+
         r29->r8+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r18+
         r29->r24+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r20
    m = permission
    p = 0
    c = c6+c5+c4+c0+c3+c1+c7
}
one sig rule1 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 2
    c = c3+c7+c0+c9+c6+c5+c8
}
one sig rule2 extends Rule{}{
    s =s5
    t =r15
    m = prohibition
    p = 1
    c = c8+c1+c9+c7+c3+c2
}
one sig rule3 extends Rule{}{
    s =s7
    t =r3
    m = prohibition
    p = 0
    c = c6+c0+c1+c7
}
one sig rule4 extends Rule{}{
    s =s1
    t =r22
    m = permission
    p = 3
    c = c5
}
one sig rule5 extends Rule{}{
    s =s20
    t =r16
    m = permission
    p = 1
    c = c7+c4+c5+c2
}
one sig rule6 extends Rule{}{
    s =s9
    t =r11
    m = prohibition
    p = 2
    c = c4+c7
}
one sig rule7 extends Rule{}{
    s =s1
    t =r14
    m = prohibition
    p = 0
    c = c6+c1+c2+c5+c4+c3
}
one sig rule8 extends Rule{}{
    s =s29
    t =r24
    m = permission
    p = 4
    c = c4+c3+c7+c6
}
one sig rule9 extends Rule{}{
    s =s19
    t =r28
    m = prohibition
    p = 0
    c = c7+c4+c8+c6+c1+c2
}
one sig rule10 extends Rule{}{
    s =s28
    t =r29
    m = permission
    p = 0
    c = c3+c7+c0+c8
}
one sig rule11 extends Rule{}{
    s =s16
    t =r6
    m = prohibition
    p = 1
    c = c7+c6+c5+c9+c8
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
