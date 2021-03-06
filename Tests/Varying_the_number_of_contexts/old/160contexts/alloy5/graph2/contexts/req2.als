module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
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
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s3+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s5+
         s9->s0+
         s9->s3+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s5+
         s12->s9+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s11+
         s13->s12+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s8+
         s15->s0+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s2+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s10+
         s17->s12+
         s17->s13+
         s18->s0+
         s18->s1+
         s18->s4+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s15+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s17+
         s21->s0+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s12+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s5+
         s22->s8+
         s22->s9+
         s22->s12+
         s22->s14+
         s22->s17+
         s22->s21+
         s23->s2+
         s23->s4+
         s23->s6+
         s23->s7+
         s23->s10+
         s23->s11+
         s23->s14+
         s23->s16+
         s23->s18+
         s23->s20+
         s24->s1+
         s24->s4+
         s24->s5+
         s24->s11+
         s24->s13+
         s24->s14+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s11+
         s25->s14+
         s25->s17+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s5+
         s26->s8+
         s26->s14+
         s26->s15+
         s26->s17+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s18+
         s27->s19+
         s27->s23+
         s27->s25+
         s28->s0+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s7+
         s28->s9+
         s28->s12+
         s28->s13+
         s28->s18+
         s28->s19+
         s28->s21+
         s28->s24+
         s28->s25+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r1+
         r3->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r4+
         r7->r0+
         r7->r3+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r7+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r8+
         r15->r9+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r20->r1+
         r20->r5+
         r20->r7+
         r20->r8+
         r20->r11+
         r20->r17+
         r20->r18+
         r21->r2+
         r21->r4+
         r21->r7+
         r21->r8+
         r21->r12+
         r21->r16+
         r21->r17+
         r21->r18+
         r22->r1+
         r22->r3+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r13+
         r22->r15+
         r22->r17+
         r22->r19+
         r23->r2+
         r23->r3+
         r23->r6+
         r23->r7+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r21+
         r24->r0+
         r24->r3+
         r24->r6+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r14+
         r24->r15+
         r24->r18+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r11+
         r25->r12+
         r25->r14+
         r25->r16+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r23+
         r25->r24+
         r26->r4+
         r26->r5+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r13+
         r26->r16+
         r26->r18+
         r26->r20+
         r26->r23+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r6+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r13+
         r27->r16+
         r27->r17+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r24+
         r28->r2+
         r28->r6+
         r28->r9+
         r28->r12+
         r28->r15+
         r28->r20+
         r28->r22+
         r28->r25+
         r28->r27+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r10+
         r29->r14+
         r29->r15+
         r29->r20+
         r29->r22+
         r29->r26+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s11
    t =r6
    m = prohibition
    p = 0
    c = c1+c0+c5+c9
}
one sig rule1 extends Rule{}{
    s =s10
    t =r14
    m = prohibition
    p = 2
    c = c1+c3+c4+c5+c7
}
one sig rule2 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 3
    c = c7+c2
}
one sig rule3 extends Rule{}{
    s =s20
    t =r6
    m = permission
    p = 0
    c = c1+c8+c3+c5+c7+c6+c4
}
one sig rule4 extends Rule{}{
    s =s11
    t =r11
    m = permission
    p = 0
    c = c3+c9
}
one sig rule5 extends Rule{}{
    s =s16
    t =r4
    m = prohibition
    p = 4
    c = c9+c7+c5+c6+c0
}
one sig rule6 extends Rule{}{
    s =s18
    t =r29
    m = prohibition
    p = 0
    c = c6+c5+c3
}
one sig rule7 extends Rule{}{
    s =s3
    t =r15
    m = prohibition
    p = 2
    c = c1+c2+c3+c0+c5
}
one sig rule8 extends Rule{}{
    s =s29
    t =r5
    m = permission
    p = 2
    c = c9+c7+c5
}
one sig rule9 extends Rule{}{
    s =s22
    t =r27
    m = permission
    p = 2
    c = c4+c9+c6+c1+c7+c8+c5
}
one sig rule10 extends Rule{}{
    s =s1
    t =r22
    m = prohibition
    p = 0
    c = c6+c1+c8+c3
}
one sig rule11 extends Rule{}{
    s =s7
    t =r10
    m = prohibition
    p = 2
    c = c8
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
run grantingContextDetermination{grantingContextDet[req2]} for 4 but 1 GrantingContext