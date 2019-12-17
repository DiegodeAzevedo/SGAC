module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s1+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s6->s0+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s1+
         s8->s2+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s9+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s7+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s12+
         s19->s14+
         s19->s15+
         s20->s5+
         s20->s6+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s6+
         s21->s7+
         s21->s11+
         s21->s13+
         s21->s15+
         s21->s17+
         s22->s4+
         s22->s5+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s18+
         s22->s19+
         s22->s21+
         s23->s3+
         s23->s6+
         s23->s12+
         s23->s15+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s11+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s20+
         s25->s24+
         s26->s0+
         s26->s4+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s14+
         s26->s17+
         s26->s20+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s2+
         s27->s4+
         s27->s11+
         s27->s12+
         s27->s14+
         s27->s15+
         s27->s18+
         s27->s20+
         s27->s21+
         s27->s24+
         s27->s26+
         s28->s3+
         s28->s4+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s15+
         s28->s16+
         s28->s18+
         s28->s20+
         s28->s22+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s6+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r4->r3+
         r5->r1+
         r6->r0+
         r6->r3+
         r7->r0+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r4+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r9+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r10+
         r14->r1+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r11+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r5+
         r16->r6+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r13+
         r17->r14+
         r18->r1+
         r18->r2+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r9+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r15+
         r20->r0+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r17+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r16+
         r22->r0+
         r22->r7+
         r22->r8+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r2+
         r23->r5+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r2+
         r24->r5+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r16+
         r25->r18+
         r25->r21+
         r25->r22+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r5+
         r26->r11+
         r26->r13+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r23+
         r26->r25+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r26+
         r28->r2+
         r28->r3+
         r28->r5+
         r28->r6+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r16+
         r28->r23+
         r28->r24+
         r28->r25+
         r29->r0+
         r29->r2+
         r29->r5+
         r29->r6+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r24+
         r29->r25+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s25
    t =r12
    m = permission
    p = 1
    c = c3+c5+c1+c4+c8+c2
}
one sig rule1 extends Rule{}{
    s =s17
    t =r7
    m = prohibition
    p = 0
    c = c4
}
one sig rule2 extends Rule{}{
    s =s29
    t =r8
    m = prohibition
    p = 3
    c = c0+c6+c2+c7+c5
}
one sig rule3 extends Rule{}{
    s =s24
    t =r19
    m = permission
    p = 3
    c = c5+c9+c8
}
one sig rule4 extends Rule{}{
    s =s15
    t =r14
    m = permission
    p = 0
    c = c8+c6+c1
}
one sig rule5 extends Rule{}{
    s =s8
    t =r6
    m = prohibition
    p = 4
    c = c9+c1+c4+c2+c6
}
one sig rule6 extends Rule{}{
    s =s23
    t =r20
    m = prohibition
    p = 1
    c = c9+c8+c2+c3+c4
}
one sig rule7 extends Rule{}{
    s =s5
    t =r19
    m = permission
    p = 3
    c = c5
}
one sig rule8 extends Rule{}{
    s =s15
    t =r20
    m = permission
    p = 3
    c = c2+c3+c0
}
one sig rule9 extends Rule{}{
    s =s10
    t =r26
    m = permission
    p = 2
    c = c2
}
one sig rule10 extends Rule{}{
    s =s7
    t =r19
    m = prohibition
    p = 3
    c = c8+c2+c9+c7+c4+c3+c5
}
one sig rule11 extends Rule{}{
    s =s10
    t =r2
    m = permission
    p = 4
    c = c8+c1+c7+c5+c6+c4
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