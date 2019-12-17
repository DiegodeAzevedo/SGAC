module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s4+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s3+
         s8->s2+
         s8->s3+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s5+
         s11->s2+
         s11->s4+
         s12->s1+
         s12->s5+
         s12->s7+
         s12->s9+
         s13->s2+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s10+
         s15->s4+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s13+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s14+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s4+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s20->s0+
         s20->s2+
         s20->s3+
         s20->s7+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s19+
         s21->s2+
         s21->s5+
         s21->s7+
         s21->s8+
         s21->s11+
         s21->s12+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s19+
         s22->s21+
         s23->s1+
         s23->s4+
         s23->s6+
         s23->s8+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s14+
         s23->s16+
         s23->s18+
         s23->s20+
         s24->s2+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s22+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s8+
         s25->s10+
         s25->s12+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s21+
         s25->s22+
         s26->s0+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s12+
         s26->s13+
         s26->s18+
         s26->s21+
         s26->s22+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s10+
         s27->s12+
         s27->s14+
         s27->s16+
         s27->s18+
         s27->s20+
         s27->s21+
         s27->s23+
         s27->s24+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s21+
         s28->s23+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s17+
         s29->s19+
         s29->s20+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r5+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r10+
         r12->r11+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r8+
         r14->r2+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r5+
         r16->r9+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r7+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r10+
         r20->r15+
         r20->r18+
         r20->r19+
         r21->r3+
         r21->r4+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r18+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r19+
         r23->r4+
         r23->r8+
         r23->r9+
         r23->r11+
         r23->r13+
         r23->r17+
         r23->r20+
         r24->r3+
         r24->r6+
         r24->r7+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r10+
         r25->r12+
         r25->r15+
         r25->r16+
         r25->r18+
         r25->r20+
         r25->r23+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r3+
         r27->r5+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r14+
         r27->r18+
         r27->r19+
         r27->r23+
         r27->r24+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r26+
         r29->r0+
         r29->r1+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r11+
         r29->r12+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r21+
         r29->r22+
         r29->r25+
         r29->r27}

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
    s =s12
    t =r18
    m = prohibition
    p = 0
    c = c6
}
one sig rule1 extends Rule{}{
    s =s23
    t =r20
    m = prohibition
    p = 2
    c = c4+c8+c6+c2
}
one sig rule2 extends Rule{}{
    s =s8
    t =r12
    m = prohibition
    p = 2
    c = c0+c5+c7+c3
}
one sig rule3 extends Rule{}{
    s =s20
    t =r13
    m = permission
    p = 3
    c = c6+c7+c3+c4+c0+c2+c9
}
one sig rule4 extends Rule{}{
    s =s24
    t =r20
    m = prohibition
    p = 2
    c = c2+c6+c1+c5+c7
}
one sig rule5 extends Rule{}{
    s =s22
    t =r19
    m = prohibition
    p = 3
    c = c0+c7+c1+c6
}
one sig rule6 extends Rule{}{
    s =s8
    t =r5
    m = permission
    p = 4
    c = c8+c3
}
one sig rule7 extends Rule{}{
    s =s28
    t =r14
    m = permission
    p = 2
    c = c2+c5
}
one sig rule8 extends Rule{}{
    s =s10
    t =r23
    m = permission
    p = 2
    c = c5
}
one sig rule9 extends Rule{}{
    s =s17
    t =r18
    m = permission
    p = 0
    c = c9+c2
}
one sig rule10 extends Rule{}{
    s =s8
    t =r25
    m = prohibition
    p = 4
    c = c7+c4
}
one sig rule11 extends Rule{}{
    s =s0
    t =r21
    m = prohibition
    p = 0
    c = c9+c3
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