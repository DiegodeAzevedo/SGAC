module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s6->s0+
         s6->s2+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s8+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s5+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s11+
         s17->s0+
         s17->s1+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s18+
         s20->s1+
         s20->s2+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s22->s4+
         s22->s10+
         s22->s12+
         s22->s14+
         s22->s16+
         s22->s17+
         s22->s18+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s8+
         s23->s16+
         s23->s17+
         s23->s20+
         s23->s22+
         s24->s1+
         s24->s3+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s16+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s1+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s10+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s21+
         s25->s23+
         s26->s0+
         s26->s2+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s18+
         s26->s21+
         s26->s22+
         s27->s0+
         s27->s4+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s24+
         s28->s1+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s21+
         s28->s23+
         s28->s25+
         s28->s26+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s7+
         s29->s8+
         s29->s11+
         s29->s14+
         s29->s15+
         s29->s18+
         s29->s20+
         s29->s22+
         s29->s23+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r5+
         r11->r0+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r3+
         r13->r5+
         r14->r4+
         r14->r5+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r11+
         r15->r13+
         r16->r1+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r3+
         r20->r6+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r13+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r6+
         r22->r7+
         r22->r12+
         r22->r16+
         r22->r17+
         r22->r19+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r16+
         r23->r17+
         r23->r19+
         r23->r20+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r18+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r9+
         r25->r13+
         r25->r15+
         r25->r21+
         r26->r2+
         r26->r6+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r15+
         r26->r18+
         r26->r20+
         r26->r22+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r17+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r26+
         r28->r0+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r11+
         r28->r13+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r24+
         r28->r26+
         r29->r0+
         r29->r4+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r18+
         r29->r21+
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
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r14
    m = prohibition
    p = 3
    c = c0+c2+c9
}
one sig rule1 extends Rule{}{
    s =s12
    t =r28
    m = prohibition
    p = 2
    c = c9
}
one sig rule2 extends Rule{}{
    s =s21
    t =r4
    m = permission
    p = 0
    c = c4+c3+c0+c9
}
one sig rule3 extends Rule{}{
    s =s25
    t =r21
    m = permission
    p = 2
    c = c7+c2+c0+c5
}
one sig rule4 extends Rule{}{
    s =s21
    t =r0
    m = permission
    p = 2
    c = c5+c6+c8+c1+c4+c0
}
one sig rule5 extends Rule{}{
    s =s13
    t =r28
    m = prohibition
    p = 0
    c = c9+c4
}
one sig rule6 extends Rule{}{
    s =s29
    t =r10
    m = permission
    p = 4
    c = c6
}
one sig rule7 extends Rule{}{
    s =s23
    t =r28
    m = permission
    p = 1
    c = c0+c9+c6+c1+c4
}
one sig rule8 extends Rule{}{
    s =s26
    t =r3
    m = prohibition
    p = 2
    c = c5
}
one sig rule9 extends Rule{}{
    s =s16
    t =r11
    m = permission
    p = 3
    c = c6+c3
}
one sig rule10 extends Rule{}{
    s =s20
    t =r21
    m = prohibition
    p = 4
    c = c4+c8+c1+c7+c5
}
one sig rule11 extends Rule{}{
    s =s27
    t =r13
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