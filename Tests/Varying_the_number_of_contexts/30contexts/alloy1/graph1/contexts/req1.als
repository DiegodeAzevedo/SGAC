module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s0+
         s5->s3+
         s6->s1+
         s7->s1+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s8+
         s11->s0+
         s11->s6+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s8+
         s13->s11+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s14+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s15+
         s19->s3+
         s19->s7+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s18+
         s20->s0+
         s20->s3+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s14+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s11+
         s21->s13+
         s21->s14+
         s22->s0+
         s22->s1+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s20+
         s23->s2+
         s23->s3+
         s23->s6+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s5+
         s24->s8+
         s24->s11+
         s24->s13+
         s24->s15+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s22+
         s25->s0+
         s25->s2+
         s25->s4+
         s25->s6+
         s25->s8+
         s25->s12+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s24+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s5+
         s26->s10+
         s26->s11+
         s26->s13+
         s26->s16+
         s26->s18+
         s26->s21+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s6+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s18+
         s27->s20+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s4+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s16+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s5+
         s29->s7+
         s29->s11+
         s29->s12+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r11+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r2+
         r15->r6+
         r15->r8+
         r15->r11+
         r16->r0+
         r16->r3+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r15+
         r19->r17+
         r20->r0+
         r20->r4+
         r20->r5+
         r20->r8+
         r20->r14+
         r20->r15+
         r21->r0+
         r21->r1+
         r21->r5+
         r21->r7+
         r21->r9+
         r21->r12+
         r21->r13+
         r21->r17+
         r21->r19+
         r22->r4+
         r22->r5+
         r22->r8+
         r22->r12+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r6+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r18+
         r24->r19+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r3+
         r25->r6+
         r25->r8+
         r25->r10+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r24+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r1+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r11+
         r27->r21+
         r27->r22+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r9+
         r28->r15+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r24+
         r28->r25+
         r29->r1+
         r29->r5+
         r29->r7+
         r29->r8+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r25}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29 extends Context{}{}

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
    s =s6
    t =r7
    m = prohibition
    p = 1
    c = c13+c0+c4+c16+c26+c2+c15+c25+c14+c6+c24+c11+c9+c19
}
one sig rule1 extends Rule{}{
    s =s29
    t =r17
    m = permission
    p = 2
    c = c21+c28+c24+c1+c27+c20+c7+c13+c15+c12+c23+c26+c18+c17+c8+c0
}
one sig rule2 extends Rule{}{
    s =s20
    t =r8
    m = permission
    p = 1
    c = c6+c14+c19+c16
}
one sig rule3 extends Rule{}{
    s =s6
    t =r27
    m = prohibition
    p = 4
    c = c16+c27+c8+c15+c0+c19+c13+c26+c11+c28
}
one sig rule4 extends Rule{}{
    s =s24
    t =r26
    m = prohibition
    p = 4
    c = c20+c26+c4+c13+c29+c0+c19
}
one sig rule5 extends Rule{}{
    s =s20
    t =r20
    m = permission
    p = 1
    c = c13+c14+c0+c3+c23+c15+c2+c17+c1+c27+c24+c16+c4
}
one sig rule6 extends Rule{}{
    s =s2
    t =r20
    m = prohibition
    p = 1
    c = c15+c12+c9+c0+c16+c25+c11+c21+c23
}
one sig rule7 extends Rule{}{
    s =s21
    t =r18
    m = permission
    p = 4
    c = c4+c6+c16+c21+c27+c29+c17+c20+c3+c0+c24+c13+c9+c28+c23
}
one sig rule8 extends Rule{}{
    s =s1
    t =r18
    m = permission
    p = 3
    c = c16+c23+c15+c2+c4+c1+c12+c17+c19+c29+c26+c5
}
one sig rule9 extends Rule{}{
    s =s20
    t =r16
    m = prohibition
    p = 4
    c = c26+c24+c12+c15+c21
}
one sig rule10 extends Rule{}{
    s =s10
    t =r13
    m = permission
    p = 0
    c = c18+c23+c27+c10+c6+c26+c22+c0+c25+c16+c8+c5+c21
}
one sig rule11 extends Rule{}{
    s =s6
    t =r14
    m = permission
    p = 0
    c = c11+c25+c12+c15
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