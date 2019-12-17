module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s7+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s0+
         s13->s2+
         s13->s4+
         s13->s6+
         s13->s11+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s9+
         s16->s11+
         s16->s13+
         s16->s14+
         s17->s2+
         s17->s3+
         s17->s6+
         s17->s9+
         s17->s11+
         s17->s13+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s11+
         s19->s12+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s16+
         s21->s0+
         s21->s3+
         s21->s4+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s14+
         s21->s15+
         s21->s17+
         s22->s3+
         s22->s5+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s18+
         s22->s19+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s11+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s5+
         s24->s8+
         s24->s9+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s20+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s9+
         s25->s11+
         s25->s13+
         s25->s15+
         s25->s17+
         s25->s19+
         s25->s20+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s13+
         s26->s17+
         s26->s19+
         s26->s21+
         s27->s0+
         s27->s4+
         s27->s5+
         s27->s8+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s19+
         s27->s20+
         s27->s23+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s13+
         s28->s14+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s25+
         s28->s27+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s8+
         s29->s12+
         s29->s14+
         s29->s16+
         s29->s18+
         s29->s21+
         s29->s23+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r2+
         r4->r1+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r6+
         r8->r2+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r15->r1+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r12+
         r17->r0+
         r17->r4+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r12+
         r19->r0+
         r19->r2+
         r19->r5+
         r19->r8+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r4+
         r20->r5+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r18+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r12+
         r21->r14+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r9+
         r22->r11+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r14+
         r23->r15+
         r23->r18+
         r23->r21+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r15+
         r24->r17+
         r24->r18+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r10+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r17+
         r25->r18+
         r25->r20+
         r26->r1+
         r26->r4+
         r26->r8+
         r26->r11+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r18+
         r26->r19+
         r26->r21+
         r26->r22+
         r26->r23+
         r27->r0+
         r27->r4+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r14+
         r27->r16+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r25+
         r28->r0+
         r28->r3+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r24+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r8+
         r29->r12+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r21+
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
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s21
    t =r0
    m = prohibition
    p = 1
    c = c7+c9+c5+c0+c1
}
one sig rule1 extends Rule{}{
    s =s26
    t =r24
    m = prohibition
    p = 3
    c = c5+c8+c1+c2+c0+c9
}
one sig rule2 extends Rule{}{
    s =s14
    t =r28
    m = permission
    p = 3
    c = c7+c3
}
one sig rule3 extends Rule{}{
    s =s14
    t =r15
    m = prohibition
    p = 4
    c = c3+c4+c5+c6+c0+c7+c2
}
one sig rule4 extends Rule{}{
    s =s25
    t =r1
    m = prohibition
    p = 2
    c = c7+c1+c0
}
one sig rule5 extends Rule{}{
    s =s20
    t =r22
    m = prohibition
    p = 0
    c = c7+c6+c9+c4
}
one sig rule6 extends Rule{}{
    s =s21
    t =r11
    m = prohibition
    p = 0
    c = c3+c4
}
one sig rule7 extends Rule{}{
    s =s27
    t =r20
    m = prohibition
    p = 1
    c = c1
}
one sig rule8 extends Rule{}{
    s =s16
    t =r28
    m = prohibition
    p = 0
    c = c5+c9+c2+c8
}
one sig rule9 extends Rule{}{
    s =s20
    t =r6
    m = prohibition
    p = 4
    c = c9+c0+c6+c5+c7+c2+c1
}
one sig rule10 extends Rule{}{
    s =s6
    t =r10
    m = permission
    p = 1
    c = c5+c2+c0+c8+c3+c6+c1
}
one sig rule11 extends Rule{}{
    s =s3
    t =r25
    m = permission
    p = 1
    c = c7+c5+c0+c9+c6+c8+c1
}
one sig rule12 extends Rule{}{
    s =s16
    t =r28
    m = permission
    p = 1
    c = c6
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