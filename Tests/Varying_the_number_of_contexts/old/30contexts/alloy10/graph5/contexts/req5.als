module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s2+
         s9->s1+
         s9->s5+
         s9->s8+
         s10->s7+
         s10->s8+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s9+
         s12->s10+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s10+
         s14->s1+
         s14->s4+
         s14->s8+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s1+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s17->s0+
         s17->s1+
         s17->s5+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s14+
         s18->s0+
         s18->s2+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s12+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s5+
         s19->s6+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s11+
         s20->s14+
         s20->s17+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s18+
         s21->s19+
         s22->s1+
         s22->s2+
         s22->s4+
         s22->s5+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s10+
         s23->s12+
         s23->s15+
         s23->s16+
         s23->s18+
         s24->s0+
         s24->s6+
         s24->s9+
         s24->s10+
         s24->s16+
         s24->s18+
         s24->s20+
         s24->s23+
         s25->s2+
         s25->s7+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s15+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s20+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s8+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s23+
         s27->s24+
         s27->s26+
         s28->s0+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s15+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s29->s2+
         s29->s10+
         s29->s11+
         s29->s24+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r5->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r8+
         r13->r9+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r6+
         r15->r7+
         r15->r14+
         r16->r1+
         r16->r3+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r17+
         r19->r2+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r20->r1+
         r20->r5+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r13+
         r20->r14+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r12+
         r21->r15+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r7+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r16+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r2+
         r23->r4+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r13+
         r23->r16+
         r23->r20+
         r24->r0+
         r24->r3+
         r24->r5+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r16+
         r24->r17+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r18+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r3+
         r26->r5+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r23+
         r26->r24+
         r27->r1+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r8+
         r27->r10+
         r27->r11+
         r27->r14+
         r27->r15+
         r27->r21+
         r27->r22+
         r27->r24+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r5+
         r28->r6+
         r28->r8+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r22+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r4+
         r29->r6+
         r29->r9+
         r29->r12+
         r29->r14+
         r29->r18+
         r29->r20+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r25+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s4
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 3
    c = c0+c4+c8+c5
}
one sig rule1 extends Rule{}{
    s =s2
    t =r16
    m = permission
    p = 4
    c = c4+c0+c3+c5+c2+c7
}
one sig rule2 extends Rule{}{
    s =s29
    t =r5
    m = prohibition
    p = 1
    c = c8
}
one sig rule3 extends Rule{}{
    s =s28
    t =r13
    m = prohibition
    p = 4
    c = c2
}
one sig rule4 extends Rule{}{
    s =s3
    t =r13
    m = prohibition
    p = 1
    c = c1+c9+c3+c7+c4+c2
}
one sig rule5 extends Rule{}{
    s =s1
    t =r9
    m = permission
    p = 4
    c = c8+c9+c0+c7+c6+c5
}
one sig rule6 extends Rule{}{
    s =s16
    t =r13
    m = permission
    p = 2
    c = c1+c6+c5+c7
}
one sig rule7 extends Rule{}{
    s =s6
    t =r22
    m = permission
    p = 3
    c = c7+c1+c0+c5
}
one sig rule8 extends Rule{}{
    s =s11
    t =r3
    m = prohibition
    p = 2
    c = c0+c9+c6
}
one sig rule9 extends Rule{}{
    s =s9
    t =r7
    m = permission
    p = 4
    c = c0+c8+c1+c2
}
one sig rule10 extends Rule{}{
    s =s6
    t =r27
    m = permission
    p = 4
    c = c3+c5+c8+c0+c4+c2+c7+c9
}
one sig rule11 extends Rule{}{
    s =s8
    t =r28
    m = permission
    p = 2
    c = c4+c1+c9
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
run grantingContextDetermination{grantingContextDet[req5]} for 4 but 1 GrantingContext