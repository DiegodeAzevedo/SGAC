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
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s4+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s4+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s3+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s13+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s5+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s15+
         s21->s19+
         s22->s0+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s23->s0+
         s23->s2+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s10+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s24->s1+
         s24->s4+
         s24->s6+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s20+
         s24->s21+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s7+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s16+
         s25->s17+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s4+
         s26->s5+
         s26->s7+
         s26->s10+
         s26->s13+
         s26->s17+
         s26->s18+
         s27->s3+
         s27->s5+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s14+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s22+
         s28->s0+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s5+
         s29->s6+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s18+
         s29->s21+
         s29->s24+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r2+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r4+
         r9->r0+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r6+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r5+
         r13->r6+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r7+
         r17->r8+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r5+
         r19->r11+
         r19->r12+
         r19->r15+
         r20->r2+
         r20->r4+
         r20->r6+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r6+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r19+
         r22->r0+
         r22->r4+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r16+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r4+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r16+
         r24->r0+
         r24->r2+
         r24->r7+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r18+
         r24->r19+
         r24->r21+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r9+
         r25->r12+
         r25->r15+
         r25->r16+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r7+
         r26->r9+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r20+
         r26->r25+
         r27->r0+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r13+
         r27->r15+
         r27->r16+
         r27->r19+
         r27->r21+
         r27->r23+
         r27->r24+
         r28->r6+
         r28->r8+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r17+
         r28->r24+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r10+
         r29->r13+
         r29->r14+
         r29->r18+
         r29->r20+
         r29->r21+
         r29->r22}

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
    s =s24
    t =r7
    m = permission
    p = 4
    c = c0+c8+c4+c1+c9+c2+c7
}
one sig rule1 extends Rule{}{
    s =s26
    t =r12
    m = permission
    p = 1
    c = c1+c0
}
one sig rule2 extends Rule{}{
    s =s13
    t =r12
    m = permission
    p = 1
    c = c1+c8+c0+c5+c6
}
one sig rule3 extends Rule{}{
    s =s27
    t =r8
    m = prohibition
    p = 1
    c = c6+c4
}
one sig rule4 extends Rule{}{
    s =s12
    t =r22
    m = prohibition
    p = 0
    c = c3+c1
}
one sig rule5 extends Rule{}{
    s =s20
    t =r7
    m = prohibition
    p = 1
    c = c2+c5+c9+c3+c8+c7+c0
}
one sig rule6 extends Rule{}{
    s =s25
    t =r5
    m = permission
    p = 3
    c = c0+c7+c6+c3+c5
}
one sig rule7 extends Rule{}{
    s =s18
    t =r14
    m = permission
    p = 4
    c = c5+c6+c4+c8+c0
}
one sig rule8 extends Rule{}{
    s =s3
    t =r16
    m = prohibition
    p = 3
    c = c7+c0+c9+c8+c2+c1+c5
}
one sig rule9 extends Rule{}{
    s =s8
    t =r19
    m = permission
    p = 1
    c = c6+c0+c1
}
one sig rule10 extends Rule{}{
    s =s20
    t =r8
    m = prohibition
    p = 0
    c = c6
}
one sig rule11 extends Rule{}{
    s =s25
    t =r11
    m = prohibition
    p = 4
    c = c9+c6+c1+c0+c5+c3
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
