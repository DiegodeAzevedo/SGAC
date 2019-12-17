module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s8->s1+
         s8->s4+
         s8->s5+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s2+
         s10->s6+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s7+
         s13->s8+
         s13->s9+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s5+
         s15->s6+
         s15->s9+
         s15->s13+
         s16->s1+
         s16->s9+
         s16->s11+
         s16->s15+
         s17->s0+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s11+
         s17->s13+
         s17->s14+
         s18->s0+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s13+
         s18->s15+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s13+
         s19->s15+
         s20->s0+
         s20->s2+
         s20->s7+
         s20->s10+
         s20->s16+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s10+
         s21->s17+
         s21->s18+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s10+
         s23->s11+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s20+
         s24->s1+
         s24->s4+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s20+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s8+
         s25->s9+
         s25->s13+
         s25->s17+
         s25->s18+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s17+
         s26->s19+
         s26->s21+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s2+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s23+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s8+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s19+
         s28->s21+
         s28->s23+
         s28->s26+
         s29->s4+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s21+
         s29->s24+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r4+
         r7->r0+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r4+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r3+
         r11->r7+
         r11->r10+
         r12->r2+
         r12->r3+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r3+
         r17->r5+
         r17->r7+
         r18->r0+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r12+
         r19->r14+
         r19->r16+
         r19->r18+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r15+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r3+
         r21->r4+
         r21->r8+
         r21->r12+
         r21->r13+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r14+
         r22->r15+
         r22->r17+
         r22->r20+
         r23->r1+
         r23->r3+
         r23->r4+
         r23->r7+
         r23->r15+
         r23->r16+
         r23->r18+
         r23->r20+
         r24->r0+
         r24->r3+
         r24->r4+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r5+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r14+
         r25->r19+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r1+
         r26->r4+
         r26->r9+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r24+
         r27->r1+
         r27->r2+
         r27->r6+
         r27->r9+
         r27->r10+
         r27->r16+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r19+
         r28->r25+
         r28->r26+
         r29->r1+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r23+
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
    s =s11
    t =r15
    m = prohibition
    p = 2
    c = c3+c2+c4+c6+c9+c5
}
one sig rule1 extends Rule{}{
    s =s25
    t =r9
    m = prohibition
    p = 0
    c = c9+c7+c1+c5
}
one sig rule2 extends Rule{}{
    s =s17
    t =r0
    m = prohibition
    p = 2
    c = c6+c1+c7+c3+c2+c5+c0
}
one sig rule3 extends Rule{}{
    s =s10
    t =r27
    m = permission
    p = 2
    c = c9+c0+c8+c7+c6+c1
}
one sig rule4 extends Rule{}{
    s =s25
    t =r19
    m = permission
    p = 1
    c = c8+c0+c5+c2
}
one sig rule5 extends Rule{}{
    s =s3
    t =r12
    m = permission
    p = 3
    c = c9+c5+c1+c7+c2+c6
}
one sig rule6 extends Rule{}{
    s =s26
    t =r20
    m = permission
    p = 0
    c = c3+c7+c9+c0+c6
}
one sig rule7 extends Rule{}{
    s =s16
    t =r7
    m = permission
    p = 0
    c = c9+c6
}
one sig rule8 extends Rule{}{
    s =s12
    t =r5
    m = prohibition
    p = 3
    c = c2
}
one sig rule9 extends Rule{}{
    s =s24
    t =r1
    m = permission
    p = 4
    c = c5+c0
}
one sig rule10 extends Rule{}{
    s =s19
    t =r13
    m = prohibition
    p = 0
    c = c5+c4+c0+c1+c2+c9+c8
}
one sig rule11 extends Rule{}{
    s =s25
    t =r1
    m = prohibition
    p = 1
    c = c9
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