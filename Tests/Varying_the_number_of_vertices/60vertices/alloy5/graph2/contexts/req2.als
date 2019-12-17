module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s1+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s8+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s7+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s7+
         s16->s9+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s11+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s3+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s16+
         s19->s17+
         s20->s1+
         s20->s5+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s18+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s8+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s18+
         s22->s19+
         s22->s21+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s7+
         s23->s8+
         s23->s14+
         s23->s18+
         s23->s21+
         s24->s1+
         s24->s3+
         s24->s6+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s10+
         s25->s11+
         s25->s13+
         s25->s17+
         s25->s20+
         s25->s23+
         s25->s24+
         s26->s2+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s21+
         s26->s22+
         s26->s24+
         s27->s0+
         s27->s2+
         s27->s7+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s5+
         s28->s8+
         s28->s11+
         s28->s12+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s23+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s12+
         s29->s14+
         s29->s18+
         s29->s20+
         s29->s21}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r2+
         r5->r0+
         r5->r2+
         r5->r3+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r5+
         r8->r0+
         r8->r3+
         r8->r5+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r10+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r8+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r16+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r11+
         r20->r16+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r6+
         r21->r7+
         r21->r10+
         r21->r15+
         r21->r17+
         r22->r1+
         r22->r4+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r23->r2+
         r23->r4+
         r23->r7+
         r23->r8+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r15+
         r23->r17+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r6+
         r24->r7+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r21+
         r24->r22+
         r25->r0+
         r25->r10+
         r25->r12+
         r25->r15+
         r25->r18+
         r25->r19+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r12+
         r26->r14+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r22+
         r27->r1+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r13+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r21+
         r27->r24+
         r27->r26+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r11+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r23+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r2+
         r29->r5+
         r29->r10+
         r29->r18+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r25+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r11
    m = prohibition
    p = 4
    c = c3+c0+c8+c5+c1
}
one sig rule1 extends Rule{}{
    s =s8
    t =r3
    m = prohibition
    p = 0
    c = c1+c2
}
one sig rule2 extends Rule{}{
    s =s18
    t =r28
    m = permission
    p = 1
    c = c8+c3+c2+c9
}
one sig rule3 extends Rule{}{
    s =s22
    t =r2
    m = permission
    p = 2
    c = c2+c1
}
one sig rule4 extends Rule{}{
    s =s10
    t =r0
    m = permission
    p = 1
    c = c9+c5+c6+c3+c0
}
one sig rule5 extends Rule{}{
    s =s25
    t =r4
    m = permission
    p = 0
    c = c6+c2+c5+c4
}
one sig rule6 extends Rule{}{
    s =s21
    t =r17
    m = prohibition
    p = 0
    c = c0+c2+c3+c1+c5+c6
}
one sig rule7 extends Rule{}{
    s =s26
    t =r20
    m = permission
    p = 3
    c = c2+c3+c7
}
one sig rule8 extends Rule{}{
    s =s1
    t =r17
    m = permission
    p = 3
    c = c0+c3+c1+c8+c4
}
one sig rule9 extends Rule{}{
    s =s0
    t =r29
    m = permission
    p = 3
    c = c1
}
one sig rule10 extends Rule{}{
    s =s10
    t =r23
    m = prohibition
    p = 2
    c = c3+c1+c9+c4
}
one sig rule11 extends Rule{}{
    s =s14
    t =r8
    m = prohibition
    p = 3
    c = c9+c4+c3
}
one sig rule12 extends Rule{}{
    s =s0
    t =r27
    m = permission
    p = 4
    c = c3+c2+c7+c5+c9+c4
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