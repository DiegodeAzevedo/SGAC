module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s4->s3+
         s5->s1+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s7+
         s9->s5+
         s10->s3+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s11+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s12+
         s18->s14+
         s18->s15+
         s19->s0+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s20->s0+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s16+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s16+
         s22->s18+
         s22->s21+
         s23->s4+
         s23->s6+
         s23->s8+
         s23->s12+
         s23->s14+
         s23->s17+
         s23->s19+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s16+
         s24->s17+
         s24->s20+
         s24->s22+
         s25->s1+
         s25->s3+
         s25->s4+
         s25->s6+
         s25->s8+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s10+
         s26->s11+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s5+
         s27->s8+
         s27->s11+
         s27->s12+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s20+
         s27->s21+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s6+
         s28->s14+
         s28->s15+
         s28->s20+
         s28->s22+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s6+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s23+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r2+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r3+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r5+
         r8->r0+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r3+
         r10->r4+
         r10->r9+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r8+
         r15->r10+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r15+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r15+
         r20->r16+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r7+
         r22->r8+
         r22->r10+
         r22->r11+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r19+
         r23->r0+
         r23->r1+
         r23->r4+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r14+
         r23->r17+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r6+
         r24->r9+
         r24->r10+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r20+
         r24->r21+
         r25->r0+
         r25->r2+
         r25->r5+
         r25->r7+
         r25->r10+
         r25->r11+
         r25->r14+
         r25->r15+
         r25->r18+
         r25->r19+
         r25->r24+
         r26->r0+
         r26->r2+
         r26->r4+
         r26->r8+
         r26->r10+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r19+
         r26->r23+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r21+
         r28->r22+
         r28->r23+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r11+
         r29->r12+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r21+
         r29->r22+
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
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r9
    m = prohibition
    p = 2
    c = c6+c1+c8+c0+c5
}
one sig rule1 extends Rule{}{
    s =s18
    t =r19
    m = permission
    p = 3
    c = c4+c7+c5+c2+c9+c0
}
one sig rule2 extends Rule{}{
    s =s24
    t =r6
    m = permission
    p = 2
    c = c4+c9
}
one sig rule3 extends Rule{}{
    s =s16
    t =r29
    m = prohibition
    p = 2
    c = c4+c9+c0+c1
}
one sig rule4 extends Rule{}{
    s =s28
    t =r27
    m = prohibition
    p = 1
    c = c7+c4+c3+c0+c5+c8
}
one sig rule5 extends Rule{}{
    s =s25
    t =r18
    m = permission
    p = 1
    c = c6+c3
}
one sig rule6 extends Rule{}{
    s =s22
    t =r4
    m = prohibition
    p = 1
    c = c1+c9+c8
}
one sig rule7 extends Rule{}{
    s =s13
    t =r9
    m = permission
    p = 1
    c = c9+c5+c8+c4+c3
}
one sig rule8 extends Rule{}{
    s =s16
    t =r6
    m = permission
    p = 0
    c = c5+c6+c0+c2
}
one sig rule9 extends Rule{}{
    s =s1
    t =r9
    m = permission
    p = 4
    c = c2+c4+c8+c9+c6
}
one sig rule10 extends Rule{}{
    s =s20
    t =r22
    m = permission
    p = 2
    c = c7+c6+c5+c1
}
one sig rule11 extends Rule{}{
    s =s28
    t =r7
    m = prohibition
    p = 3
    c = c0+c6+c3+c4+c9+c1
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
run grantingContextDetermination{grantingContextDet[req2]} for 4 but 1 GrantingContext