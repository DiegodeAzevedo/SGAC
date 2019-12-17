module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s6+
         s8->s1+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s7+
         s9->s8+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s14+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s6+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s0+
         s20->s3+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s16+
         s20->s17+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s5+
         s21->s9+
         s21->s11+
         s21->s16+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s12+
         s22->s14+
         s22->s18+
         s23->s0+
         s23->s2+
         s23->s8+
         s23->s9+
         s23->s14+
         s23->s15+
         s23->s18+
         s23->s19+
         s23->s21+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s14+
         s24->s15+
         s24->s18+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s7+
         s25->s12+
         s25->s14+
         s25->s19+
         s25->s20+
         s25->s21+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s19+
         s26->s20+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s11+
         s27->s13+
         s27->s14+
         s27->s17+
         s27->s22+
         s27->s23+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s7+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s16+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s2+
         s29->s6+
         s29->s10+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s20+
         s29->s23+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r4->r3+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r7+
         r10->r5+
         r10->r7+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r4+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r11+
         r15->r13+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r10+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r14+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r17+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r4+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r15+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r4+
         r23->r6+
         r23->r10+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r17+
         r23->r18+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r11+
         r24->r12+
         r24->r18+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r12+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r5+
         r26->r7+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r19+
         r26->r21+
         r26->r23+
         r26->r24+
         r27->r4+
         r27->r6+
         r27->r9+
         r27->r15+
         r27->r17+
         r27->r18+
         r27->r22+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r5+
         r28->r13+
         r28->r15+
         r28->r20+
         r28->r21+
         r29->r7+
         r29->r8+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r15+
         r29->r16+
         r29->r19+
         r29->r21+
         r29->r22+
         r29->r24+
         r29->r26+
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
    s =s19
    t =r5
    m = prohibition
    p = 3
    c = c9+c3+c7+c4+c1
}
one sig rule1 extends Rule{}{
    s =s2
    t =r20
    m = prohibition
    p = 2
    c = c5
}
one sig rule2 extends Rule{}{
    s =s5
    t =r4
    m = permission
    p = 2
    c = c9+c8+c1+c7+c5
}
one sig rule3 extends Rule{}{
    s =s29
    t =r5
    m = permission
    p = 2
    c = c9+c0
}
one sig rule4 extends Rule{}{
    s =s10
    t =r16
    m = prohibition
    p = 3
    c = c4
}
one sig rule5 extends Rule{}{
    s =s13
    t =r25
    m = permission
    p = 1
    c = c8+c5+c6
}
one sig rule6 extends Rule{}{
    s =s13
    t =r1
    m = permission
    p = 2
    c = c3
}
one sig rule7 extends Rule{}{
    s =s28
    t =r19
    m = permission
    p = 4
    c = c9+c3+c7+c1
}
one sig rule8 extends Rule{}{
    s =s27
    t =r11
    m = permission
    p = 4
    c = c6+c0+c4+c7+c9+c1
}
one sig rule9 extends Rule{}{
    s =s28
    t =r7
    m = prohibition
    p = 4
    c = c9+c6+c0+c4+c7+c3
}
one sig rule10 extends Rule{}{
    s =s28
    t =r7
    m = permission
    p = 1
    c = c9+c2+c1+c6
}
one sig rule11 extends Rule{}{
    s =s4
    t =r19
    m = prohibition
    p = 0
    c = c1+c3+c4
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