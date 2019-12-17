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
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s4+
         s6->s5+
         s7->s4+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s12->s1+
         s12->s4+
         s12->s6+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s10+
         s19->s0+
         s19->s4+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13+
         s20->s0+
         s20->s3+
         s20->s4+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s18+
         s21->s1+
         s21->s4+
         s21->s6+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s13+
         s22->s14+
         s22->s18+
         s22->s20+
         s23->s0+
         s23->s4+
         s23->s6+
         s23->s12+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s4+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s15+
         s24->s16+
         s24->s18+
         s24->s22+
         s25->s1+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s17+
         s25->s19+
         s25->s20+
         s25->s23+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s6+
         s26->s7+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s17+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s2+
         s27->s3+
         s27->s15+
         s27->s16+
         s27->s19+
         s27->s22+
         s27->s23+
         s27->s25+
         s28->s1+
         s28->s5+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s9+
         s29->s10+
         s29->s14+
         s29->s18+
         s29->s19+
         s29->s24+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r9->r2+
         r9->r4+
         r9->r6+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r9+
         r13->r10+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r13+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r14+
         r17->r15+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r6+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r18+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r15+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r8+
         r21->r10+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r19+
         r22->r1+
         r22->r3+
         r22->r6+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r17+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r9+
         r23->r12+
         r23->r13+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r8+
         r24->r9+
         r24->r12+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r20+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r8+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r18+
         r25->r20+
         r25->r24+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r5+
         r26->r8+
         r26->r9+
         r26->r11+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r20+
         r26->r21+
         r26->r24+
         r27->r0+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r15+
         r27->r16+
         r27->r19+
         r27->r23+
         r27->r25+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r13+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r25+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r8+
         r29->r9+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r25+
         r29->r26+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s1
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r3
    m = prohibition
    p = 3
    c = c5+c0+c1
}
one sig rule1 extends Rule{}{
    s =s24
    t =r22
    m = permission
    p = 4
    c = c3+c2+c8+c5+c0+c6+c1
}
one sig rule2 extends Rule{}{
    s =s12
    t =r24
    m = prohibition
    p = 2
    c = c1+c7+c8
}
one sig rule3 extends Rule{}{
    s =s15
    t =r26
    m = prohibition
    p = 0
    c = c7+c3+c9+c0+c5
}
one sig rule4 extends Rule{}{
    s =s0
    t =r17
    m = prohibition
    p = 1
    c = c1+c7+c3+c8+c4
}
one sig rule5 extends Rule{}{
    s =s15
    t =r12
    m = permission
    p = 4
    c = c6+c7+c2+c4
}
one sig rule6 extends Rule{}{
    s =s10
    t =r20
    m = prohibition
    p = 2
    c = c6+c0+c1+c3+c9
}
one sig rule7 extends Rule{}{
    s =s19
    t =r1
    m = prohibition
    p = 0
    c = c3+c0+c8+c5
}
one sig rule8 extends Rule{}{
    s =s11
    t =r25
    m = permission
    p = 0
    c = c0+c5
}
one sig rule9 extends Rule{}{
    s =s6
    t =r26
    m = prohibition
    p = 2
    c = c4+c1+c0+c7
}
one sig rule10 extends Rule{}{
    s =s12
    t =r9
    m = prohibition
    p = 3
    c = c6+c2+c0+c7
}
one sig rule11 extends Rule{}{
    s =s25
    t =r4
    m = prohibition
    p = 2
    c = c0+c5+c6+c2+c8+c1
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