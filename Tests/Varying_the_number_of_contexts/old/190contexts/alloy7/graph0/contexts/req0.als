module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s5+
         s8->s2+
         s8->s5+
         s8->s6+
         s9->s1+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s10+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s3+
         s18->s7+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s13+
         s19->s17+
         s20->s1+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s19+
         s21->s1+
         s21->s3+
         s21->s4+
         s21->s7+
         s21->s12+
         s21->s13+
         s21->s16+
         s21->s18+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s15+
         s22->s17+
         s22->s18+
         s22->s20+
         s23->s0+
         s23->s4+
         s23->s5+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s21+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s12+
         s24->s14+
         s24->s16+
         s24->s18+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s1+
         s25->s3+
         s25->s8+
         s25->s10+
         s25->s11+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s21+
         s25->s23+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s9+
         s26->s10+
         s26->s13+
         s26->s14+
         s26->s17+
         s26->s19+
         s26->s23+
         s26->s25+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s8+
         s27->s9+
         s27->s13+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s21+
         s27->s23+
         s28->s0+
         s28->s2+
         s28->s6+
         s28->s8+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s20+
         s28->s23+
         s28->s25+
         s29->s2+
         s29->s5+
         s29->s6+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s15+
         s29->s17+
         s29->s20+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r3+
         r6->r1+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r5+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r7+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r8+
         r13->r0+
         r13->r3+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r8+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r14+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r17+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r0+
         r23->r2+
         r23->r7+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r15+
         r23->r17+
         r24->r1+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r17+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r13+
         r25->r16+
         r25->r17+
         r25->r19+
         r26->r1+
         r26->r5+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r17+
         r26->r18+
         r26->r23+
         r26->r24+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r12+
         r27->r13+
         r27->r15+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r23+
         r27->r24+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r26+
         r29->r2+
         r29->r5+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r18+
         r29->r19+
         r29->r21+
         r29->r24+
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
    s =s4
    t =r22
    m = permission
    p = 4
    c = c8+c0+c1+c5+c6+c9+c7
}
one sig rule1 extends Rule{}{
    s =s3
    t =r10
    m = prohibition
    p = 0
    c = c5+c6+c0+c8+c1+c9
}
one sig rule2 extends Rule{}{
    s =s13
    t =r27
    m = prohibition
    p = 3
    c = c7
}
one sig rule3 extends Rule{}{
    s =s18
    t =r11
    m = prohibition
    p = 3
    c = c1+c4+c9+c6+c3
}
one sig rule4 extends Rule{}{
    s =s26
    t =r5
    m = permission
    p = 4
    c = c3
}
one sig rule5 extends Rule{}{
    s =s13
    t =r9
    m = prohibition
    p = 2
    c = c4+c5
}
one sig rule6 extends Rule{}{
    s =s22
    t =r13
    m = permission
    p = 0
    c = c2+c1
}
one sig rule7 extends Rule{}{
    s =s16
    t =r19
    m = permission
    p = 2
    c = c4+c2+c3+c9
}
one sig rule8 extends Rule{}{
    s =s6
    t =r5
    m = permission
    p = 1
    c = c7+c3
}
one sig rule9 extends Rule{}{
    s =s5
    t =r11
    m = permission
    p = 4
    c = c3+c0+c9+c5+c4+c7+c6+c1
}
one sig rule10 extends Rule{}{
    s =s12
    t =r11
    m = permission
    p = 1
    c = c0+c8+c3+c9+c5
}
one sig rule11 extends Rule{}{
    s =s21
    t =r9
    m = prohibition
    p = 4
    c = c3+c1+c7+c8+c4
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