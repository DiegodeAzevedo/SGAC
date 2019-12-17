module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s2+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s6+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s8+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s12+
         s16->s13+
         s17->s4+
         s17->s7+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s19->s1+
         s19->s2+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s8+
         s20->s9+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s7+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s21+
         s23->s1+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s16+
         s23->s20+
         s23->s21+
         s24->s0+
         s24->s2+
         s24->s8+
         s24->s9+
         s24->s13+
         s24->s16+
         s24->s17+
         s24->s18+
         s25->s2+
         s25->s3+
         s25->s11+
         s25->s13+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s2+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s17+
         s26->s18+
         s26->s20+
         s26->s22+
         s26->s23+
         s26->s24+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s9+
         s27->s14+
         s27->s16+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s23+
         s27->s24+
         s27->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r7+
         r15->r10+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r15+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r15+
         r21->r16+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r18+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r15+
         r23->r16+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r14+
         r24->r15+
         r24->r16+
         r25->r1+
         r25->r5+
         r25->r8+
         r25->r9+
         r25->r13+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r24+
         r26->r1+
         r26->r4+
         r26->r8+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r15+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r24}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s1
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r13
    m = prohibition
    p = 4
    c = c0+c9+c6+c1+c4
}
one sig rule1 extends Rule{}{
    s =s7
    t =r8
    m = prohibition
    p = 3
    c = c6+c3+c1+c7+c4+c0+c9
}
one sig rule2 extends Rule{}{
    s =s12
    t =r25
    m = prohibition
    p = 0
    c = c1+c7+c8+c2
}
one sig rule3 extends Rule{}{
    s =s3
    t =r15
    m = permission
    p = 4
    c = c6+c8
}
one sig rule4 extends Rule{}{
    s =s25
    t =r13
    m = prohibition
    p = 0
    c = c1+c5
}
one sig rule5 extends Rule{}{
    s =s13
    t =r21
    m = permission
    p = 3
    c = c4+c6+c5+c7+c0
}
one sig rule6 extends Rule{}{
    s =s10
    t =r16
    m = prohibition
    p = 0
    c = c2+c5+c6+c3
}
one sig rule7 extends Rule{}{
    s =s12
    t =r25
    m = prohibition
    p = 4
    c = c4+c2+c1+c6
}
one sig rule8 extends Rule{}{
    s =s14
    t =r25
    m = permission
    p = 3
    c = c3+c2+c1+c5
}
one sig rule9 extends Rule{}{
    s =s18
    t =r25
    m = prohibition
    p = 0
    c = c7+c9+c6+c3
}
one sig rule10 extends Rule{}{
    s =s26
    t =r24
    m = prohibition
    p = 4
    c = c0
}
one sig rule11 extends Rule{}{
    s =s16
    t =r13
    m = prohibition
    p = 3
    c = c3
}
one sig rule12 extends Rule{}{
    s =s4
    t =r12
    m = permission
    p = 1
    c = c0+c9+c4+c1+c5+c7
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