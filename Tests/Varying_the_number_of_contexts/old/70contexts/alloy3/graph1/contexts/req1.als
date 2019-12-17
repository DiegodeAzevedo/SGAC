module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s4+
         s9->s6+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s3+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s5+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s18->s1+
         s18->s4+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s15+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s14+
         s20->s16+
         s20->s17+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s14+
         s21->s15+
         s21->s18+
         s22->s2+
         s22->s4+
         s22->s5+
         s22->s8+
         s22->s10+
         s22->s14+
         s22->s15+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s4+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s17+
         s23->s19+
         s23->s20+
         s24->s0+
         s24->s2+
         s24->s5+
         s24->s6+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s20+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s6+
         s25->s8+
         s25->s14+
         s25->s19+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s13+
         s26->s14+
         s26->s17+
         s26->s19+
         s26->s22+
         s26->s24+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s13+
         s27->s14+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s22+
         s27->s24+
         s28->s2+
         s28->s3+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s11+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s4+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s12+
         s29->s17+
         s29->s21+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r5->r4+
         r6->r0+
         r6->r5+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r3+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r6+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r4+
         r14->r7+
         r14->r11+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r15+
         r19->r17+
         r20->r2+
         r20->r4+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r19+
         r21->r2+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r12+
         r22->r14+
         r22->r15+
         r22->r17+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r15+
         r23->r16+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r8+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r21+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r19+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r2+
         r26->r5+
         r26->r12+
         r26->r13+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r21+
         r26->r23+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r8+
         r27->r10+
         r27->r15+
         r27->r16+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r15+
         r28->r17+
         r28->r19+
         r28->r26+
         r28->r27+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r14+
         r29->r16+
         r29->r18+
         r29->r20+
         r29->r22+
         r29->r23}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r21
    m = permission
    p = 1
    c = c3+c6+c2
}
one sig rule1 extends Rule{}{
    s =s5
    t =r16
    m = prohibition
    p = 1
    c = c4+c3+c0+c1+c7+c5
}
one sig rule2 extends Rule{}{
    s =s13
    t =r11
    m = permission
    p = 2
    c = c6+c0+c2+c8+c3+c5+c1
}
one sig rule3 extends Rule{}{
    s =s13
    t =r9
    m = permission
    p = 0
    c = c1+c2+c7+c9
}
one sig rule4 extends Rule{}{
    s =s3
    t =r21
    m = permission
    p = 2
    c = c7+c2+c6+c1
}
one sig rule5 extends Rule{}{
    s =s13
    t =r18
    m = permission
    p = 4
    c = c9+c2+c3
}
one sig rule6 extends Rule{}{
    s =s24
    t =r26
    m = permission
    p = 2
    c = c7+c6+c2+c9+c0+c8+c3+c4+c1
}
one sig rule7 extends Rule{}{
    s =s6
    t =r15
    m = permission
    p = 4
    c = c5
}
one sig rule8 extends Rule{}{
    s =s10
    t =r20
    m = prohibition
    p = 3
    c = c8+c4+c0+c2+c6
}
one sig rule9 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 3
    c = c0+c3
}
one sig rule10 extends Rule{}{
    s =s21
    t =r10
    m = prohibition
    p = 3
    c = c1+c6+c0
}
one sig rule11 extends Rule{}{
    s =s24
    t =r26
    m = prohibition
    p = 3
    c = c5+c0+c4+c1+c6
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