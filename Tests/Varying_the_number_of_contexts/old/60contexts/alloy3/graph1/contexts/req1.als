module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
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
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s2+
         s7->s1+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s7+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s3+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s8+
         s17->s10+
         s17->s14+
         s18->s0+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s7+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s15+
         s20->s0+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s9+
         s20->s13+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s19+
         s21->s2+
         s21->s3+
         s21->s8+
         s21->s9+
         s21->s15+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s7+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s14+
         s23->s18+
         s23->s19+
         s24->s0+
         s24->s1+
         s24->s6+
         s24->s8+
         s24->s10+
         s24->s11+
         s24->s14+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s16+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s6+
         s26->s8+
         s26->s11+
         s26->s14+
         s26->s17+
         s26->s20+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s12+
         s27->s14+
         s27->s16+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s1+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s14+
         s28->s16+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s23+
         s28->s27+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s17+
         s29->s20+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r2+
         r4->r2+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r3+
         r7->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r3+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r7+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r8+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r14+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r16+
         r19->r17+
         r20->r0+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r19+
         r21->r2+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r10+
         r21->r11+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r3+
         r23->r4+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r12+
         r23->r18+
         r23->r19+
         r23->r21+
         r24->r0+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r18+
         r24->r19+
         r24->r22+
         r24->r23+
         r25->r2+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r15+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r13+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r21+
         r26->r22+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r9+
         r27->r10+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r20+
         r27->r21+
         r27->r23+
         r27->r24+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r7+
         r28->r11+
         r28->r14+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r26+
         r28->r27+
         r29->r6+
         r29->r8+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r15+
         r29->r16+
         r29->r20+
         r29->r22+
         r29->r24+
         r29->r26}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r25
    m = permission
    p = 3
    c = c3+c1
}
one sig rule1 extends Rule{}{
    s =s24
    t =r9
    m = permission
    p = 0
    c = c3+c2+c4+c1+c6+c8+c7+c5
}
one sig rule2 extends Rule{}{
    s =s3
    t =r19
    m = prohibition
    p = 1
    c = c0+c8+c6+c5+c3+c9+c2
}
one sig rule3 extends Rule{}{
    s =s23
    t =r15
    m = prohibition
    p = 2
    c = c7
}
one sig rule4 extends Rule{}{
    s =s21
    t =r24
    m = permission
    p = 0
    c = c9
}
one sig rule5 extends Rule{}{
    s =s11
    t =r18
    m = permission
    p = 0
    c = c2+c1+c9+c5+c4
}
one sig rule6 extends Rule{}{
    s =s0
    t =r26
    m = prohibition
    p = 4
    c = c6+c2+c8+c0+c1+c4+c5
}
one sig rule7 extends Rule{}{
    s =s10
    t =r11
    m = prohibition
    p = 0
    c = c1+c7+c6+c2+c4
}
one sig rule8 extends Rule{}{
    s =s11
    t =r6
    m = permission
    p = 1
    c = c4+c2+c9+c7+c5+c8+c1
}
one sig rule9 extends Rule{}{
    s =s8
    t =r24
    m = prohibition
    p = 4
    c = c9+c2+c3+c6+c8+c5
}
one sig rule10 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 2
    c = c4+c8+c3+c9+c0+c5+c6
}
one sig rule11 extends Rule{}{
    s =s22
    t =r7
    m = prohibition
    p = 3
    c = c7
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
run grantingContextDetermination{grantingContextDet[req1]} for 4 but 1 GrantingContext