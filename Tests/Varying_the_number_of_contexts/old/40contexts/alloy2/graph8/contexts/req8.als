module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s3+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s1+
         s13->s4+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s11+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s11+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s16+
         s19->s8+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s17+
         s20->s1+
         s20->s3+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s19+
         s21->s2+
         s21->s4+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s17+
         s21->s19+
         s22->s0+
         s22->s3+
         s22->s5+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s3+
         s23->s5+
         s23->s6+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s4+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s15+
         s24->s16+
         s24->s18+
         s24->s19+
         s24->s22+
         s25->s0+
         s25->s3+
         s25->s8+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s22+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s7+
         s26->s10+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s19+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s24+
         s27->s1+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s16+
         s27->s18+
         s27->s21+
         s27->s22+
         s27->s24+
         s28->s0+
         s28->s5+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s18+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s25+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s22+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r4->r2+
         r5->r0+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r2+
         r8->r0+
         r8->r4+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r3+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r6+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r4+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r11+
         r18->r13+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r8+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r19+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r7+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r8+
         r23->r10+
         r23->r14+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r22+
         r24->r0+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r18+
         r25->r2+
         r25->r3+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r9+
         r25->r12+
         r25->r13+
         r25->r16+
         r25->r19+
         r25->r22+
         r25->r24+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r16+
         r26->r18+
         r26->r21+
         r26->r22+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r15+
         r27->r16+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r13+
         r28->r15+
         r28->r17+
         r28->r20+
         r28->r22+
         r28->r27+
         r29->r3+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r24}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req8 extends Request{}{
sub=s2
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s22
    t =r20
    m = prohibition
    p = 4
    c = c0+c7+c5+c2+c4
}
one sig rule1 extends Rule{}{
    s =s8
    t =r18
    m = prohibition
    p = 1
    c = c6+c1+c2+c0+c7
}
one sig rule2 extends Rule{}{
    s =s1
    t =r27
    m = prohibition
    p = 2
    c = c2+c5+c3+c0+c7+c6
}
one sig rule3 extends Rule{}{
    s =s5
    t =r10
    m = prohibition
    p = 3
    c = c9+c3+c2+c5
}
one sig rule4 extends Rule{}{
    s =s10
    t =r21
    m = permission
    p = 1
    c = c1+c5+c0
}
one sig rule5 extends Rule{}{
    s =s29
    t =r7
    m = permission
    p = 4
    c = c6+c5+c1+c9+c4+c7
}
one sig rule6 extends Rule{}{
    s =s28
    t =r27
    m = permission
    p = 0
    c = c6+c2+c8+c1+c5+c7
}
one sig rule7 extends Rule{}{
    s =s8
    t =r13
    m = permission
    p = 4
    c = c9+c6+c3
}
one sig rule8 extends Rule{}{
    s =s19
    t =r15
    m = prohibition
    p = 2
    c = c5+c7+c2+c4+c3+c6+c0+c9
}
one sig rule9 extends Rule{}{
    s =s13
    t =r2
    m = permission
    p = 2
    c = c6+c3+c0+c2+c8
}
one sig rule10 extends Rule{}{
    s =s5
    t =r22
    m = permission
    p = 1
    c = c4+c7+c1+c6+c9+c8
}
one sig rule11 extends Rule{}{
    s =s12
    t =r6
    m = prohibition
    p = 2
    c = c2+c8+c6+c4+c9+c5
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
run grantingContextDetermination{grantingContextDet[req8]} for 4 but 1 GrantingContext