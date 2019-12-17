module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s1+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s2+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s8+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s3+
         s12->s4+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s10+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s15->s2+
         s15->s6+
         s15->s7+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s10+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s7+
         s21->s9+
         s21->s11+
         s21->s15+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s7+
         s23->s11+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s20+
         s23->s22+
         s24->s2+
         s24->s5+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s14+
         s24->s19+
         s24->s20+
         s24->s21+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s0+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s12+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s20+
         s26->s24+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s14+
         s27->s17+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s4+
         s28->s14+
         s28->s20+
         s28->s24+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s9+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s23+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r2+
         r10->r6+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r10+
         r19->r12+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r8+
         r20->r11+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r10+
         r21->r12+
         r21->r15+
         r21->r17+
         r22->r0+
         r22->r1+
         r22->r4+
         r22->r7+
         r22->r9+
         r22->r10+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r11+
         r23->r13+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r10+
         r24->r13+
         r24->r17+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r8+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r24+
         r26->r0+
         r26->r3+
         r26->r4+
         r26->r9+
         r26->r12+
         r26->r17+
         r26->r19+
         r26->r20+
         r26->r23+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r9+
         r27->r11+
         r27->r12+
         r27->r15+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r25+
         r27->r26+
         r28->r2+
         r28->r3+
         r28->r7+
         r28->r8+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r27+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r23+
         r29->r24+
         r29->r26}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r23
    m = permission
    p = 4
    c = c1+c7+c2+c8
}
one sig rule1 extends Rule{}{
    s =s22
    t =r9
    m = prohibition
    p = 3
    c = c7+c1
}
one sig rule2 extends Rule{}{
    s =s17
    t =r4
    m = prohibition
    p = 0
    c = c4
}
one sig rule3 extends Rule{}{
    s =s15
    t =r22
    m = permission
    p = 1
    c = c7+c4+c9+c2+c1+c5+c3
}
one sig rule4 extends Rule{}{
    s =s23
    t =r8
    m = permission
    p = 0
    c = c0+c2+c8+c9
}
one sig rule5 extends Rule{}{
    s =s1
    t =r22
    m = permission
    p = 0
    c = c4+c5+c6+c0+c9
}
one sig rule6 extends Rule{}{
    s =s6
    t =r9
    m = permission
    p = 0
    c = c3
}
one sig rule7 extends Rule{}{
    s =s19
    t =r7
    m = prohibition
    p = 3
    c = c6+c8+c9+c4
}
one sig rule8 extends Rule{}{
    s =s21
    t =r13
    m = prohibition
    p = 0
    c = c1+c3+c5
}
one sig rule9 extends Rule{}{
    s =s29
    t =r8
    m = prohibition
    p = 3
    c = c5+c9
}
one sig rule10 extends Rule{}{
    s =s0
    t =r29
    m = prohibition
    p = 4
    c = c5
}
one sig rule11 extends Rule{}{
    s =s0
    t =r28
    m = permission
    p = 2
    c = c6+c0+c1+c9+c2+c7+c5+c8
}
one sig rule12 extends Rule{}{
    s =s22
    t =r2
    m = prohibition
    p = 1
    c = c1+c5+c4+c8
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
run grantingContextDetermination{grantingContextDet[req1]} for 4 but 1 GrantingContext