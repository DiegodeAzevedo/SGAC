module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
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
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s3+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s6+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s11+
         s14->s2+
         s14->s4+
         s14->s7+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s9+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s17->s0+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s4+
         s18->s10+
         s18->s13+
         s18->s15+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s16+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s7+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s11+
         s21->s14+
         s21->s17+
         s21->s18+
         s22->s1+
         s22->s3+
         s22->s6+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s19+
         s23->s0+
         s23->s4+
         s23->s6+
         s23->s9+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s19+
         s24->s0+
         s24->s2+
         s24->s4+
         s24->s9+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s21+
         s24->s23+
         s25->s2+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s20+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s4+
         s26->s8+
         s26->s10+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s21+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s18+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s1+
         s28->s7+
         s28->s15+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s5+
         s29->s6+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s17+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r4+
         r7->r6+
         r8->r3+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r5+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r3+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r10+
         r14->r2+
         r14->r4+
         r14->r7+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r8+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r15+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r11+
         r19->r14+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r6+
         r20->r9+
         r20->r11+
         r20->r13+
         r20->r18+
         r21->r2+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r18+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r9+
         r22->r11+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r4+
         r23->r6+
         r23->r7+
         r23->r8+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r3+
         r24->r4+
         r24->r7+
         r24->r8+
         r24->r11+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r7+
         r25->r10+
         r25->r13+
         r25->r14+
         r25->r16+
         r25->r18+
         r25->r19+
         r25->r21+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r3+
         r26->r8+
         r26->r11+
         r26->r16+
         r26->r17+
         r26->r20+
         r26->r22+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r11+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r19+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r5+
         r28->r6+
         r28->r8+
         r28->r11+
         r28->r13+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r3+
         r29->r4+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r11+
         r29->r12+
         r29->r19+
         r29->r20+
         r29->r23+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r12
    m = permission
    p = 1
    c = c7+c2
}
one sig rule1 extends Rule{}{
    s =s10
    t =r7
    m = prohibition
    p = 0
    c = c8+c2+c6+c5+c4
}
one sig rule2 extends Rule{}{
    s =s17
    t =r21
    m = permission
    p = 3
    c = c2+c0+c7
}
one sig rule3 extends Rule{}{
    s =s19
    t =r16
    m = permission
    p = 0
    c = c8+c5+c0+c4+c1+c6
}
one sig rule4 extends Rule{}{
    s =s29
    t =r9
    m = permission
    p = 2
    c = c7+c1+c9+c6+c0
}
one sig rule5 extends Rule{}{
    s =s3
    t =r15
    m = permission
    p = 3
    c = c1+c4+c6+c8+c7+c3
}
one sig rule6 extends Rule{}{
    s =s21
    t =r26
    m = prohibition
    p = 0
    c = c2+c6+c5+c0+c9+c8
}
one sig rule7 extends Rule{}{
    s =s18
    t =r3
    m = permission
    p = 2
    c = c2+c8+c0+c1+c3
}
one sig rule8 extends Rule{}{
    s =s27
    t =r22
    m = prohibition
    p = 3
    c = c8
}
one sig rule9 extends Rule{}{
    s =s9
    t =r5
    m = permission
    p = 1
    c = c2+c4+c9
}
one sig rule10 extends Rule{}{
    s =s11
    t =r5
    m = permission
    p = 0
    c = c8+c0
}
one sig rule11 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 1
    c = c1+c2+c6+c3+c4+c5
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