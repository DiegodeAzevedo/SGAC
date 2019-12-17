module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s2+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s6->s3+
         s6->s5+
         s7->s3+
         s7->s4+
         s8->s2+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s3+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s6+
         s12->s8+
         s13->s7+
         s13->s8+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s17+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s20->s1+
         s20->s6+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s17+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s15+
         s21->s17+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s5+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s23->s0+
         s23->s3+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s17+
         s23->s19+
         s23->s21+
         s24->s0+
         s24->s4+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s22+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s23+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s8+
         s26->s11+
         s26->s12+
         s26->s16+
         s26->s18+
         s26->s22+
         s26->s24+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s9+
         s27->s11+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s6+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s17+
         s28->s19+
         s28->s24+
         s28->s25+
         s29->s1+
         s29->s2+
         s29->s5+
         s29->s8+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s17+
         s29->s20+
         s29->s25+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r3->r2+
         r4->r2+
         r4->r3+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r10+
         r12->r11+
         r13->r4+
         r13->r8+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r7+
         r14->r8+
         r14->r9+
         r15->r0+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r5+
         r17->r9+
         r17->r11+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r7+
         r19->r15+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r2+
         r20->r4+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r14+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r11+
         r21->r14+
         r21->r16+
         r21->r17+
         r22->r1+
         r22->r5+
         r22->r6+
         r22->r11+
         r22->r15+
         r22->r16+
         r22->r18+
         r22->r21+
         r23->r6+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r20+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r12+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r14+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r5+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r18+
         r26->r21+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r4+
         r27->r5+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r15+
         r27->r22+
         r27->r25+
         r28->r2+
         r28->r4+
         r28->r9+
         r28->r10+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r20+
         r28->r21+
         r28->r24+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r20+
         r29->r22+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s22
    t =r22
    m = prohibition
    p = 3
    c = c0+c9+c8+c4
}
one sig rule1 extends Rule{}{
    s =s24
    t =r8
    m = permission
    p = 3
    c = c5+c3+c2+c1
}
one sig rule2 extends Rule{}{
    s =s24
    t =r18
    m = permission
    p = 1
    c = c9+c3+c5+c1+c0+c4
}
one sig rule3 extends Rule{}{
    s =s9
    t =r0
    m = prohibition
    p = 1
    c = c3+c8+c9+c7+c1+c2+c0
}
one sig rule4 extends Rule{}{
    s =s14
    t =r5
    m = prohibition
    p = 2
    c = c9+c0+c3+c7
}
one sig rule5 extends Rule{}{
    s =s22
    t =r23
    m = prohibition
    p = 2
    c = c1+c4+c3+c7+c2
}
one sig rule6 extends Rule{}{
    s =s16
    t =r4
    m = prohibition
    p = 4
    c = c9+c0+c1+c5
}
one sig rule7 extends Rule{}{
    s =s6
    t =r29
    m = prohibition
    p = 1
    c = c0+c4
}
one sig rule8 extends Rule{}{
    s =s0
    t =r1
    m = prohibition
    p = 3
    c = c7+c9
}
one sig rule9 extends Rule{}{
    s =s7
    t =r26
    m = permission
    p = 1
    c = c9+c8+c4
}
one sig rule10 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 4
    c = c6+c0+c9+c1+c4
}
one sig rule11 extends Rule{}{
    s =s5
    t =r9
    m = prohibition
    p = 3
    c = c6+c2+c4+c3+c0
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