module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s1+
         s4->s0+
         s4->s3+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s3+
         s6->s4+
         s7->s2+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s6+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s4+
         s14->s5+
         s14->s9+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s16+
         s19->s0+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s18+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s11+
         s22->s15+
         s22->s17+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s1+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s17+
         s23->s22+
         s24->s1+
         s24->s2+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s18+
         s24->s19+
         s24->s20+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s10+
         s25->s17+
         s25->s20+
         s25->s23+
         s26->s0+
         s26->s3+
         s26->s4+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s19+
         s26->s22+
         s26->s25+
         s27->s0+
         s27->s3+
         s27->s13+
         s27->s14+
         s27->s20+
         s27->s21+
         s27->s23+
         s28->s0+
         s28->s5+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s16+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s5+
         s29->s6+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s23+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r2+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r5+
         r9->r7+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r4+
         r11->r7+
         r11->r8+
         r12->r0+
         r12->r6+
         r12->r9+
         r12->r11+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r6+
         r19->r8+
         r19->r13+
         r19->r14+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r14+
         r21->r20+
         r22->r0+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r1+
         r23->r3+
         r23->r4+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r18+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r14+
         r24->r19+
         r24->r21+
         r25->r1+
         r25->r4+
         r25->r6+
         r25->r9+
         r25->r10+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r21+
         r26->r0+
         r26->r4+
         r26->r9+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r1+
         r28->r2+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r24+
         r28->r25+
         r29->r0+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r6+
         r29->r12+
         r29->r16+
         r29->r17+
         r29->r20+
         r29->r22+
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
    s =s15
    t =r28
    m = prohibition
    p = 4
    c = c1+c0+c3+c4
}
one sig rule1 extends Rule{}{
    s =s24
    t =r9
    m = permission
    p = 3
    c = c6+c9
}
one sig rule2 extends Rule{}{
    s =s15
    t =r22
    m = permission
    p = 4
    c = c5+c1+c9+c6+c8
}
one sig rule3 extends Rule{}{
    s =s21
    t =r8
    m = prohibition
    p = 3
    c = c0+c2+c1+c6+c7+c5+c9
}
one sig rule4 extends Rule{}{
    s =s5
    t =r26
    m = prohibition
    p = 1
    c = c3+c8+c1+c7+c6
}
one sig rule5 extends Rule{}{
    s =s5
    t =r14
    m = permission
    p = 0
    c = c6+c4+c9+c7+c5+c1
}
one sig rule6 extends Rule{}{
    s =s24
    t =r20
    m = prohibition
    p = 4
    c = c3+c7+c5
}
one sig rule7 extends Rule{}{
    s =s24
    t =r5
    m = prohibition
    p = 2
    c = c6
}
one sig rule8 extends Rule{}{
    s =s21
    t =r27
    m = permission
    p = 0
    c = c1+c4+c5+c7+c0+c6+c9
}
one sig rule9 extends Rule{}{
    s =s7
    t =r26
    m = permission
    p = 1
    c = c5+c2
}
one sig rule10 extends Rule{}{
    s =s27
    t =r9
    m = permission
    p = 2
    c = c9+c8
}
one sig rule11 extends Rule{}{
    s =s5
    t =r2
    m = permission
    p = 0
    c = c9+c3+c0+c6+c7+c5
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
