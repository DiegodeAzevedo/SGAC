module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s4->s3+
         s5->s0+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s6+
         s13->s11+
         s14->s3+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s8+
         s15->s9+
         s15->s11+
         s16->s0+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s15+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s6+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s18+
         s20->s1+
         s20->s4+
         s20->s5+
         s20->s10+
         s20->s13+
         s20->s15+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s2+
         s21->s5+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s7+
         s22->s10+
         s22->s13+
         s22->s16+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s9+
         s23->s13+
         s23->s18+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s20+
         s24->s21+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s6+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s17+
         s25->s20+
         s25->s21+
         s25->s23+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s5+
         s26->s12+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s13+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s26+
         s28->s3+
         s28->s4+
         s28->s6+
         s28->s9+
         s28->s10+
         s28->s12+
         s28->s14+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s17+
         s29->s18+
         s29->s20+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r4->r1+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r7+
         r12->r10+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r7+
         r16->r9+
         r16->r12+
         r17->r1+
         r17->r3+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r15+
         r18->r1+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r14+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r17+
         r20->r0+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r18+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r14+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r4+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r19+
         r22->r21+
         r23->r0+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r13+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r10+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r19+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r10+
         r25->r12+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r22+
         r25->r24+
         r26->r0+
         r26->r3+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r11+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r20+
         r26->r22+
         r27->r1+
         r27->r4+
         r27->r5+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r13+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r24+
         r27->r25+
         r28->r0+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r2+
         r29->r4+
         r29->r7+
         r29->r8+
         r29->r9+
         r29->r12+
         r29->r13+
         r29->r16+
         r29->r18+
         r29->r19+
         r29->r23+
         r29->r24+
         r29->r26+
         r29->r27+
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
    s =s19
    t =r15
    m = prohibition
    p = 2
    c = c0+c6+c8+c7+c4+c3+c9
}
one sig rule1 extends Rule{}{
    s =s2
    t =r19
    m = prohibition
    p = 2
    c = c0+c6+c3+c7
}
one sig rule2 extends Rule{}{
    s =s13
    t =r2
    m = prohibition
    p = 2
    c = c0+c1+c4+c5+c3+c2+c6
}
one sig rule3 extends Rule{}{
    s =s16
    t =r0
    m = permission
    p = 1
    c = c3
}
one sig rule4 extends Rule{}{
    s =s11
    t =r6
    m = prohibition
    p = 4
    c = c5+c6+c7
}
one sig rule5 extends Rule{}{
    s =s9
    t =r11
    m = permission
    p = 0
    c = c0+c8+c5+c2+c9+c1
}
one sig rule6 extends Rule{}{
    s =s3
    t =r20
    m = permission
    p = 2
    c = c5+c7+c8+c4
}
one sig rule7 extends Rule{}{
    s =s1
    t =r19
    m = prohibition
    p = 3
    c = c3+c4+c0+c6+c7+c8
}
one sig rule8 extends Rule{}{
    s =s11
    t =r7
    m = permission
    p = 2
    c = c0
}
one sig rule9 extends Rule{}{
    s =s3
    t =r1
    m = permission
    p = 1
    c = c7+c2+c6+c3+c5+c1
}
one sig rule10 extends Rule{}{
    s =s2
    t =r20
    m = prohibition
    p = 2
    c = c0+c4+c8+c1+c2+c6+c5
}
one sig rule11 extends Rule{}{
    s =s1
    t =r14
    m = permission
    p = 1
    c = c6+c9+c3
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