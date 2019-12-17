module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s4+
         s12->s7+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s8+
         s14->s0+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s9+
         s15->s12+
         s15->s14+
         s16->s2+
         s16->s4+
         s16->s9+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s4+
         s18->s5+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s3+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s3+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s4+
         s22->s6+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s17+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s4+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s13+
         s24->s15+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s8+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s19+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s1+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s14+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s16+
         s28->s19+
         s28->s20+
         s28->s23+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s11+
         s29->s13+
         s29->s15+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r2+
         r11->r5+
         r11->r6+
         r12->r1+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r6+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r14+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r20->r1+
         r20->r4+
         r20->r6+
         r20->r10+
         r20->r11+
         r20->r14+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r19+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r22+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r22+
         r26->r24+
         r27->r1+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r7+
         r28->r9+
         r28->r13+
         r28->r16+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r23+
         r28->r26+
         r28->r27+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r14+
         r29->r16+
         r29->r20+
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
    s =s22
    t =r17
    m = permission
    p = 3
    c = c9
}
one sig rule1 extends Rule{}{
    s =s27
    t =r9
    m = prohibition
    p = 3
    c = c4+c7+c2+c5
}
one sig rule2 extends Rule{}{
    s =s7
    t =r27
    m = permission
    p = 4
    c = c9+c2+c4+c1
}
one sig rule3 extends Rule{}{
    s =s27
    t =r23
    m = prohibition
    p = 0
    c = c4+c5+c3+c6+c7+c2+c1+c0
}
one sig rule4 extends Rule{}{
    s =s14
    t =r6
    m = prohibition
    p = 0
    c = c3+c4+c6+c0+c5+c8+c2
}
one sig rule5 extends Rule{}{
    s =s2
    t =r3
    m = permission
    p = 0
    c = c4
}
one sig rule6 extends Rule{}{
    s =s24
    t =r22
    m = prohibition
    p = 0
    c = c0+c8+c7+c6+c9
}
one sig rule7 extends Rule{}{
    s =s23
    t =r17
    m = prohibition
    p = 0
    c = c5+c6+c2+c7+c4+c8+c3
}
one sig rule8 extends Rule{}{
    s =s10
    t =r22
    m = permission
    p = 3
    c = c7+c9
}
one sig rule9 extends Rule{}{
    s =s9
    t =r16
    m = prohibition
    p = 1
    c = c8+c1
}
one sig rule10 extends Rule{}{
    s =s1
    t =r4
    m = prohibition
    p = 0
    c = c4+c1
}
one sig rule11 extends Rule{}{
    s =s24
    t =r16
    m = prohibition
    p = 3
    c = c9+c6+c3
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