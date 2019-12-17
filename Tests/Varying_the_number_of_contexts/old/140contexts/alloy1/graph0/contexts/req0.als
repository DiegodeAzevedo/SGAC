module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s3+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s5+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s6+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s3+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s14+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s16+
         s19->s18+
         s20->s4+
         s20->s5+
         s20->s7+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s5+
         s21->s11+
         s21->s12+
         s21->s20+
         s22->s0+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s10+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s9+
         s23->s11+
         s23->s12+
         s23->s15+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s7+
         s24->s8+
         s24->s14+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s22+
         s24->s23+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s9+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s17+
         s25->s19+
         s25->s20+
         s25->s24+
         s26->s2+
         s26->s3+
         s26->s9+
         s26->s10+
         s26->s12+
         s26->s17+
         s26->s19+
         s26->s20+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s17+
         s27->s21+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s26+
         s29->s3+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s14+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s25+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r7+
         r10->r0+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r8+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r13+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r13+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r14+
         r17->r16+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r4+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r16+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r5+
         r21->r10+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r20+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r13+
         r22->r15+
         r22->r20+
         r23->r0+
         r23->r3+
         r23->r4+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r15+
         r23->r18+
         r24->r4+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r17+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r10+
         r25->r13+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r22+
         r25->r24+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r8+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r22+
         r26->r24+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r16+
         r27->r18+
         r27->r22+
         r27->r23+
         r27->r26+
         r28->r0+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r17+
         r28->r18+
         r28->r24+
         r28->r27+
         r29->r4+
         r29->r5+
         r29->r8+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r19+
         r29->r23+
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
    s =s20
    t =r1
    m = prohibition
    p = 1
    c = c7
}
one sig rule1 extends Rule{}{
    s =s9
    t =r6
    m = prohibition
    p = 0
    c = c4+c6+c8+c1
}
one sig rule2 extends Rule{}{
    s =s11
    t =r21
    m = permission
    p = 2
    c = c1+c2+c6+c3+c5+c0
}
one sig rule3 extends Rule{}{
    s =s18
    t =r0
    m = prohibition
    p = 1
    c = c5+c7+c3+c8
}
one sig rule4 extends Rule{}{
    s =s14
    t =r18
    m = permission
    p = 2
    c = c7+c4+c3+c2+c6+c5+c8+c9
}
one sig rule5 extends Rule{}{
    s =s0
    t =r6
    m = prohibition
    p = 1
    c = c6+c4+c9+c2+c3+c5
}
one sig rule6 extends Rule{}{
    s =s1
    t =r20
    m = prohibition
    p = 0
    c = c4+c7+c6+c8+c0
}
one sig rule7 extends Rule{}{
    s =s10
    t =r28
    m = permission
    p = 4
    c = c0+c7+c2+c1+c3+c8+c6
}
one sig rule8 extends Rule{}{
    s =s12
    t =r11
    m = permission
    p = 2
    c = c8+c9+c2+c3
}
one sig rule9 extends Rule{}{
    s =s29
    t =r16
    m = permission
    p = 3
    c = c6+c7+c9+c5
}
one sig rule10 extends Rule{}{
    s =s25
    t =r20
    m = prohibition
    p = 0
    c = c1+c3+c7
}
one sig rule11 extends Rule{}{
    s =s7
    t =r16
    m = permission
    p = 2
    c = c3+c7+c1+c6+c2
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