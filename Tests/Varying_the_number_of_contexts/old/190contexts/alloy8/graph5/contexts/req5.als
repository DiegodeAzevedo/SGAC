module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s4->s2+
         s4->s3+
         s5->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s2+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s7+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s2+
         s12->s8+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s8+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s9+
         s15->s10+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s6+
         s16->s10+
         s16->s11+
         s16->s15+
         s17->s3+
         s17->s4+
         s17->s8+
         s17->s11+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s15+
         s19->s1+
         s19->s6+
         s19->s9+
         s19->s14+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s16+
         s20->s17+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s12+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s19+
         s22->s0+
         s22->s2+
         s22->s4+
         s22->s6+
         s22->s9+
         s22->s11+
         s22->s13+
         s22->s18+
         s22->s19+
         s23->s1+
         s23->s2+
         s23->s8+
         s23->s13+
         s23->s16+
         s23->s19+
         s23->s20+
         s24->s0+
         s24->s2+
         s24->s4+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s3+
         s26->s7+
         s26->s8+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s23+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s6+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s14+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s26+
         s28->s0+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s14+
         s28->s17+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s1+
         s29->s3+
         s29->s4+
         s29->s9+
         s29->s14+
         s29->s16+
         s29->s18+
         s29->s23+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r6+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r3+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r4+
         r13->r6+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r11+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r7+
         r17->r11+
         r17->r12+
         r17->r15+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r8+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r17+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r13+
         r20->r15+
         r20->r18+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r11+
         r21->r12+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r12+
         r23->r13+
         r23->r17+
         r23->r18+
         r23->r20+
         r24->r0+
         r24->r3+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r20+
         r24->r21+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r14+
         r25->r16+
         r25->r18+
         r25->r21+
         r25->r24+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r18+
         r26->r22+
         r26->r23+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r6+
         r27->r9+
         r27->r10+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r21+
         r27->r22+
         r27->r24+
         r28->r0+
         r28->r1+
         r28->r4+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r23+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r4+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r13+
         r29->r14+
         r29->r18+
         r29->r19+
         r29->r21+
         r29->r23+
         r29->r24+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s1
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 0
    c = c5+c1+c6+c8+c4+c9
}
one sig rule1 extends Rule{}{
    s =s3
    t =r25
    m = prohibition
    p = 4
    c = c9+c5+c1+c0
}
one sig rule2 extends Rule{}{
    s =s9
    t =r21
    m = prohibition
    p = 2
    c = c0+c6
}
one sig rule3 extends Rule{}{
    s =s22
    t =r16
    m = prohibition
    p = 3
    c = c4+c7+c9
}
one sig rule4 extends Rule{}{
    s =s23
    t =r2
    m = permission
    p = 4
    c = c3+c9+c6+c0
}
one sig rule5 extends Rule{}{
    s =s21
    t =r22
    m = permission
    p = 3
    c = c1+c4+c9+c0+c5+c8
}
one sig rule6 extends Rule{}{
    s =s20
    t =r27
    m = permission
    p = 2
    c = c1+c6+c8+c5+c4
}
one sig rule7 extends Rule{}{
    s =s25
    t =r29
    m = prohibition
    p = 0
    c = c9+c2+c4+c1+c6
}
one sig rule8 extends Rule{}{
    s =s18
    t =r10
    m = permission
    p = 1
    c = c6+c4+c3+c5+c8
}
one sig rule9 extends Rule{}{
    s =s6
    t =r4
    m = prohibition
    p = 1
    c = c2+c4+c6
}
one sig rule10 extends Rule{}{
    s =s3
    t =r3
    m = permission
    p = 2
    c = c8
}
one sig rule11 extends Rule{}{
    s =s3
    t =r18
    m = prohibition
    p = 2
    c = c7+c9+c3
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