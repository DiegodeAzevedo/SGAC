module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s2+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s2+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s2+
         s8->s3+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s13->s2+
         s13->s3+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s9+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s10+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s6+
         s17->s8+
         s17->s13+
         s17->s15+
         s18->s2+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s13+
         s18->s16+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s13+
         s19->s15+
         s19->s18+
         s20->s0+
         s20->s7+
         s20->s8+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s18+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s4+
         s22->s6+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s16+
         s22->s18+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s5+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s13+
         s24->s14+
         s24->s18+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s8+
         s25->s9+
         s25->s10+
         s25->s13+
         s25->s14+
         s25->s17+
         s25->s21+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s7+
         s26->s10+
         s26->s14+
         s26->s21+
         s26->s22+
         s26->s23+
         s27->s1+
         s27->s3+
         s27->s4+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s21+
         s27->s22+
         s28->s0+
         s28->s4+
         s28->s6+
         s28->s7+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s20+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s2+
         s29->s4+
         s29->s6+
         s29->s8+
         s29->s14+
         s29->s15+
         s29->s18+
         s29->s20+
         s29->s24+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r8->r2+
         r8->r7+
         r9->r3+
         r9->r4+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r14->r0+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r14+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r14+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r6+
         r19->r8+
         r19->r12+
         r19->r13+
         r19->r16+
         r19->r17+
         r20->r2+
         r20->r10+
         r20->r14+
         r20->r15+
         r20->r17+
         r21->r0+
         r21->r2+
         r21->r6+
         r21->r10+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r19+
         r22->r0+
         r22->r4+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r17+
         r23->r3+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r12+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r24->r3+
         r24->r4+
         r24->r7+
         r24->r10+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r6+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r19+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r8+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r17+
         r26->r19+
         r26->r24+
         r27->r4+
         r27->r8+
         r27->r9+
         r27->r12+
         r27->r13+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r25+
         r27->r26+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r10+
         r28->r14+
         r28->r15+
         r28->r17+
         r28->r20+
         r28->r21+
         r29->r2+
         r29->r5+
         r29->r7+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r17+
         r29->r22+
         r29->r24+
         r29->r25+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s27
    t =r0
    m = permission
    p = 2
    c = c3+c5+c7+c8+c0
}
one sig rule1 extends Rule{}{
    s =s29
    t =r18
    m = prohibition
    p = 4
    c = c7+c8+c5
}
one sig rule2 extends Rule{}{
    s =s18
    t =r2
    m = prohibition
    p = 1
    c = c7+c2+c3+c1
}
one sig rule3 extends Rule{}{
    s =s25
    t =r20
    m = prohibition
    p = 1
    c = c7+c6+c5+c8+c2+c9+c1
}
one sig rule4 extends Rule{}{
    s =s22
    t =r1
    m = permission
    p = 4
    c = c3
}
one sig rule5 extends Rule{}{
    s =s24
    t =r14
    m = permission
    p = 2
    c = c4+c6+c8+c2+c7
}
one sig rule6 extends Rule{}{
    s =s16
    t =r0
    m = prohibition
    p = 0
    c = c3+c4+c8
}
one sig rule7 extends Rule{}{
    s =s14
    t =r28
    m = permission
    p = 4
    c = c4+c3+c2+c8
}
one sig rule8 extends Rule{}{
    s =s18
    t =r22
    m = prohibition
    p = 0
    c = c2+c0
}
one sig rule9 extends Rule{}{
    s =s0
    t =r11
    m = permission
    p = 4
    c = c5+c8+c7
}
one sig rule10 extends Rule{}{
    s =s20
    t =r29
    m = prohibition
    p = 3
    c = c0+c6+c7+c3+c4+c9+c2
}
one sig rule11 extends Rule{}{
    s =s8
    t =r6
    m = prohibition
    p = 2
    c = c9+c8+c3+c0
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