module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s6+
         s8->s0+
         s8->s4+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s5+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17+
         s20->s0+
         s20->s4+
         s20->s7+
         s20->s8+
         s20->s14+
         s20->s15+
         s21->s4+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s15+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s16+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s7+
         s24->s10+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s18+
         s24->s20+
         s24->s21+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s21+
         s25->s23+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s9+
         s26->s11+
         s26->s14+
         s26->s18+
         s26->s20+
         s26->s22+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s11+
         s27->s12+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s10+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s18+
         s28->s22+
         s28->s23+
         s28->s26+
         s28->s27+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s5+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s22+
         s29->s23+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r4+
         r9->r1+
         r9->r2+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r15->r4+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r5+
         r16->r7+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r3+
         r17->r6+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r12+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r17+
         r20->r1+
         r20->r3+
         r20->r7+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r16+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r4+
         r21->r11+
         r21->r14+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r1+
         r22->r8+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r3+
         r23->r4+
         r23->r12+
         r23->r13+
         r23->r16+
         r23->r18+
         r24->r6+
         r24->r10+
         r24->r11+
         r24->r14+
         r24->r15+
         r24->r22+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r14+
         r25->r15+
         r25->r18+
         r25->r20+
         r25->r21+
         r26->r0+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r12+
         r26->r13+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r0+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r6+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r17+
         r27->r18+
         r27->r21+
         r27->r23+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r7+
         r28->r9+
         r28->r10+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r26+
         r29->r1+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r9+
         r29->r11+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r18+
         r29->r19+
         r29->r20+
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
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r2
    m = prohibition
    p = 4
    c = c8+c3+c2+c1+c5
}
one sig rule1 extends Rule{}{
    s =s12
    t =r2
    m = prohibition
    p = 4
    c = c1+c0
}
one sig rule2 extends Rule{}{
    s =s11
    t =r13
    m = prohibition
    p = 1
    c = c8+c3+c4
}
one sig rule3 extends Rule{}{
    s =s8
    t =r10
    m = permission
    p = 0
    c = c4+c2+c3+c8+c0+c9+c1
}
one sig rule4 extends Rule{}{
    s =s16
    t =r23
    m = prohibition
    p = 0
    c = c8+c4+c6+c9+c2+c0
}
one sig rule5 extends Rule{}{
    s =s14
    t =r5
    m = permission
    p = 3
    c = c4+c0+c1+c6+c3+c7
}
one sig rule6 extends Rule{}{
    s =s26
    t =r25
    m = prohibition
    p = 4
    c = c0+c9+c3+c6
}
one sig rule7 extends Rule{}{
    s =s8
    t =r4
    m = prohibition
    p = 2
    c = c3+c1+c8+c4
}
one sig rule8 extends Rule{}{
    s =s7
    t =r4
    m = prohibition
    p = 4
    c = c0+c5+c4+c9
}
one sig rule9 extends Rule{}{
    s =s28
    t =r18
    m = permission
    p = 3
    c = c5+c0+c1+c3+c8
}
one sig rule10 extends Rule{}{
    s =s10
    t =r19
    m = prohibition
    p = 1
    c = c3+c2+c0+c6
}
one sig rule11 extends Rule{}{
    s =s3
    t =r10
    m = prohibition
    p = 0
    c = c1+c2
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