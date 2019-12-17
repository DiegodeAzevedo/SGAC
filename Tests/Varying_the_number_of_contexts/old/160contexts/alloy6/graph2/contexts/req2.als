module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s1+
         s5->s3+
         s6->s1+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s4+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s9+
         s12->s10+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s14+
         s17->s15+
         s18->s4+
         s18->s6+
         s18->s10+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s7+
         s19->s8+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s14+
         s20->s15+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s2+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s12+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s19+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s8+
         s22->s11+
         s22->s13+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s7+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s19+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s18+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s1+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s13+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s25+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s10+
         s28->s11+
         s28->s14+
         s28->s20+
         s28->s22+
         s28->s23+
         s29->s1+
         s29->s5+
         s29->s6+
         s29->s9+
         s29->s10+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r5->r1+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r5+
         r9->r0+
         r9->r2+
         r9->r5+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r8+
         r14->r11+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r11+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r5+
         r19->r9+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r18+
         r20->r0+
         r20->r4+
         r20->r5+
         r20->r8+
         r20->r9+
         r20->r13+
         r20->r17+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r4+
         r21->r6+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r16+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r8+
         r22->r16+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r8+
         r24->r11+
         r24->r13+
         r24->r18+
         r24->r19+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r17+
         r25->r19+
         r25->r23+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r7+
         r27->r11+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r22+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r3+
         r28->r9+
         r28->r10+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r24+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r10+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r18+
         r29->r21+
         r29->r23+
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
one sig req2 extends Request{}{
sub=s0
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r24
    m = prohibition
    p = 0
    c = c4+c3+c5+c8
}
one sig rule1 extends Rule{}{
    s =s1
    t =r0
    m = permission
    p = 4
    c = c8+c3+c0+c7+c9+c5
}
one sig rule2 extends Rule{}{
    s =s21
    t =r2
    m = prohibition
    p = 2
    c = c1+c5+c8+c4
}
one sig rule3 extends Rule{}{
    s =s15
    t =r27
    m = prohibition
    p = 3
    c = c0+c2+c1+c5+c7+c3
}
one sig rule4 extends Rule{}{
    s =s19
    t =r28
    m = permission
    p = 0
    c = c2+c6+c8
}
one sig rule5 extends Rule{}{
    s =s2
    t =r8
    m = permission
    p = 3
    c = c7+c8+c9
}
one sig rule6 extends Rule{}{
    s =s8
    t =r10
    m = prohibition
    p = 3
    c = c3+c4+c5+c8+c1+c2
}
one sig rule7 extends Rule{}{
    s =s10
    t =r10
    m = permission
    p = 4
    c = c4+c7+c3
}
one sig rule8 extends Rule{}{
    s =s13
    t =r10
    m = prohibition
    p = 4
    c = c7+c3
}
one sig rule9 extends Rule{}{
    s =s23
    t =r10
    m = permission
    p = 0
    c = c2+c8+c7+c0+c4
}
one sig rule10 extends Rule{}{
    s =s19
    t =r29
    m = prohibition
    p = 2
    c = c3+c0+c6
}
one sig rule11 extends Rule{}{
    s =s15
    t =r25
    m = permission
    p = 2
    c = c7
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