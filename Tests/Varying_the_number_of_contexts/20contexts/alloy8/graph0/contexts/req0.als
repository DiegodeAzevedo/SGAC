module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
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
         s4->s1+
         s5->s1+
         s5->s2+
         s6->s0+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s8+
         s12->s9+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s6+
         s14->s7+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s7+
         s19->s13+
         s19->s14+
         s19->s16+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s12+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s15+
         s22->s18+
         s22->s19+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s5+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s17+
         s23->s19+
         s23->s21+
         s23->s22+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s7+
         s24->s8+
         s24->s10+
         s24->s13+
         s24->s16+
         s24->s17+
         s24->s21+
         s24->s22+
         s25->s1+
         s25->s4+
         s25->s5+
         s25->s13+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s22+
         s26->s1+
         s26->s2+
         s26->s8+
         s26->s11+
         s26->s12+
         s26->s15+
         s26->s16+
         s26->s19+
         s26->s21+
         s26->s23+
         s27->s2+
         s27->s4+
         s27->s7+
         s27->s8+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s18+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s18+
         s28->s21+
         s28->s22+
         s28->s25+
         s29->s0+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s20+
         s29->s22+
         s29->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r4->r0+
         r4->r1+
         r5->r0+
         r5->r1+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r4+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r3+
         r11->r5+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r2+
         r13->r7+
         r13->r10+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r8+
         r15->r4+
         r15->r5+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r15+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r16+
         r19->r1+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r14+
         r20->r17+
         r20->r18+
         r21->r1+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r9+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r20+
         r22->r2+
         r22->r3+
         r22->r8+
         r22->r12+
         r22->r13+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r22+
         r24->r0+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r11+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r20+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r7+
         r25->r8+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r4+
         r26->r5+
         r26->r8+
         r26->r10+
         r26->r12+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r21+
         r26->r22+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r5+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r12+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r8+
         r28->r11+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r23+
         r28->r26+
         r29->r2+
         r29->r4+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r11+
         r29->r13+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r23+
         r29->r24+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19 extends Context{}{}

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
    s =s13
    t =r19
    m = prohibition
    p = 3
    c = c14+c0
}
one sig rule1 extends Rule{}{
    s =s3
    t =r12
    m = permission
    p = 2
    c = c17+c1+c18+c8+c2+c5+c12+c0
}
one sig rule2 extends Rule{}{
    s =s9
    t =r28
    m = prohibition
    p = 3
    c = c16
}
one sig rule3 extends Rule{}{
    s =s4
    t =r27
    m = permission
    p = 3
    c = c17+c0+c15+c11+c1+c5+c7+c6+c2+c18+c3
}
one sig rule4 extends Rule{}{
    s =s3
    t =r7
    m = prohibition
    p = 0
    c = c15+c3+c5+c6+c17+c9+c0+c2+c11
}
one sig rule5 extends Rule{}{
    s =s3
    t =r14
    m = prohibition
    p = 2
    c = c4+c6+c14+c18
}
one sig rule6 extends Rule{}{
    s =s17
    t =r22
    m = prohibition
    p = 1
    c = c4+c8+c5+c6+c3+c17+c7+c18+c9+c1+c13
}
one sig rule7 extends Rule{}{
    s =s15
    t =r19
    m = permission
    p = 1
    c = c7+c2+c4+c10+c8+c0+c13+c16
}
one sig rule8 extends Rule{}{
    s =s26
    t =r8
    m = prohibition
    p = 0
    c = c16+c11+c13+c8+c15+c3+c1+c12
}
one sig rule9 extends Rule{}{
    s =s1
    t =r21
    m = prohibition
    p = 3
    c = c4+c0+c2+c6+c5+c9+c16
}
one sig rule10 extends Rule{}{
    s =s7
    t =r22
    m = permission
    p = 2
    c = c17+c14+c6+c8+c2+c11+c7+c12+c19+c9+c10+c16+c5
}
one sig rule11 extends Rule{}{
    s =s22
    t =r3
    m = prohibition
    p = 2
    c = c12+c13+c10+c14+c3+c0+c9+c19+c15+c8+c5
}
//**************************
//***Auxiliary Predicates***
//**************************
pred access_condition[req:Request,con:Context]{
    (no  r:applicableRules[req] |  (evalRuleCond[r,con] and r.m=prohibition and
        all rule: r.^(req.ruleSucc) | not evalRuleCond[rule,con])	)
    and some { r:applicableRules[req] |evalRuleCond[r,con]}
}

//***************************
//***Determination of the ***
//***conditions (contexts)***
//***************************

one sig GrantingContext{
        acc: set Context
}{}

pred grantingContextDet[req:Request]{
        all c: Context | access_condition[req,c] <=> c in GrantingContext.acc
}
//*** determination command ***
run grantingContextDetermination{grantingContextDet[req0]} for 4 but 1 GrantingContext