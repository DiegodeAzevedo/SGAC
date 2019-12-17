module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s2+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s5+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s7+
         s10->s9+
         s11->s4+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s13->s2+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s10+
         s16->s11+
         s16->s12+
         s17->s2+
         s17->s3+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s16+
         s19->s6+
         s19->s7+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s16+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s13+
         s20->s15+
         s20->s16+
         s20->s19+
         s21->s2+
         s21->s4+
         s21->s6+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s6+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s17+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s8+
         s23->s10+
         s23->s13+
         s23->s14+
         s23->s18+
         s23->s19+
         s23->s22+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s18+
         s24->s20+
         s24->s23+
         s25->s1+
         s25->s4+
         s25->s7+
         s25->s9+
         s25->s11+
         s25->s16+
         s25->s17+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s2+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s12+
         s26->s14+
         s26->s16+
         s26->s18+
         s26->s19+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s3+
         s27->s4+
         s27->s8+
         s27->s9+
         s27->s11+
         s27->s16+
         s27->s17+
         s27->s18+
         s28->s4+
         s28->s5+
         s28->s8+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s23+
         s28->s24+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s7+
         s29->s9+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s22+
         s29->s23+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r3+
         r6->r0+
         r7->r0+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r8+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r6+
         r12->r7+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r8+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r15->r2+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r6+
         r16->r7+
         r16->r10+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r12+
         r20->r14+
         r20->r17+
         r20->r18+
         r21->r1+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r16+
         r21->r19+
         r21->r20+
         r22->r1+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r12+
         r22->r14+
         r22->r20+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r14+
         r23->r18+
         r23->r19+
         r24->r1+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r11+
         r24->r21+
         r24->r23+
         r25->r2+
         r25->r4+
         r25->r7+
         r25->r9+
         r25->r11+
         r25->r14+
         r25->r16+
         r25->r18+
         r25->r20+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r8+
         r26->r11+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r19+
         r26->r25+
         r27->r2+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r15+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r24+
         r27->r25+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r29->r0+
         r29->r2+
         r29->r7+
         r29->r12+
         r29->r16+
         r29->r18+
         r29->r26+
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
    s =s3
    t =r19
    m = prohibition
    p = 0
    c = c8+c1+c4+c0+c5+c2+c9
}
one sig rule1 extends Rule{}{
    s =s26
    t =r2
    m = prohibition
    p = 4
    c = c4
}
one sig rule2 extends Rule{}{
    s =s14
    t =r2
    m = prohibition
    p = 1
    c = c8+c1+c6+c3
}
one sig rule3 extends Rule{}{
    s =s14
    t =r27
    m = prohibition
    p = 0
    c = c1+c2+c9+c3+c6+c5
}
one sig rule4 extends Rule{}{
    s =s12
    t =r19
    m = prohibition
    p = 1
    c = c7+c9+c6
}
one sig rule5 extends Rule{}{
    s =s23
    t =r11
    m = permission
    p = 1
    c = c7+c2+c4+c3+c9
}
one sig rule6 extends Rule{}{
    s =s4
    t =r16
    m = prohibition
    p = 4
    c = c3+c6+c5+c1+c8
}
one sig rule7 extends Rule{}{
    s =s21
    t =r4
    m = prohibition
    p = 2
    c = c1+c7+c5+c3
}
one sig rule8 extends Rule{}{
    s =s7
    t =r10
    m = prohibition
    p = 1
    c = c4+c2
}
one sig rule9 extends Rule{}{
    s =s10
    t =r2
    m = permission
    p = 1
    c = c1+c7
}
one sig rule10 extends Rule{}{
    s =s11
    t =r8
    m = permission
    p = 3
    c = c1+c9+c4+c3+c0+c5
}
one sig rule11 extends Rule{}{
    s =s24
    t =r28
    m = permission
    p = 1
    c = c8+c4+c1+c5+c7+c6+c9
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