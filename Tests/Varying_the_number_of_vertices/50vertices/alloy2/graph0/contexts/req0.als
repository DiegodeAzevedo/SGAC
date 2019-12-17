module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s4+
         s8->s2+
         s8->s3+
         s8->s5+
         s9->s2+
         s10->s3+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s4+
         s12->s5+
         s12->s6+
         s13->s0+
         s13->s2+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s10+
         s14->s11+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s13+
         s16->s3+
         s16->s6+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s3+
         s17->s8+
         s17->s9+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s15+
         s20->s2+
         s20->s3+
         s20->s6+
         s20->s7+
         s20->s10+
         s20->s14+
         s20->s15+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s19+
         s22->s21+
         s23->s3+
         s23->s5+
         s23->s7+
         s23->s11+
         s23->s12+
         s23->s14+
         s23->s16+
         s23->s18+
         s23->s20+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s12+
         s24->s13+
         s24->s15+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r2+
         r6->r5+
         r7->r1+
         r7->r6+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r5+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r6+
         r10->r8+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r8+
         r13->r11+
         r14->r1+
         r14->r4+
         r14->r7+
         r14->r9+
         r14->r11+
         r15->r0+
         r15->r2+
         r15->r5+
         r15->r8+
         r15->r12+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r3+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r13+
         r20->r16+
         r20->r17+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r12+
         r21->r15+
         r21->r17+
         r21->r18+
         r21->r20+
         r22->r2+
         r22->r4+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r15+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r8+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r18+
         r24->r21}

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
    t =r19
    m = prohibition
    p = 1
    c = c6+c2+c9+c5+c0
}
one sig rule1 extends Rule{}{
    s =s10
    t =r15
    m = prohibition
    p = 3
    c = c4+c1
}
one sig rule2 extends Rule{}{
    s =s20
    t =r0
    m = permission
    p = 4
    c = c5+c1+c8
}
one sig rule3 extends Rule{}{
    s =s7
    t =r23
    m = prohibition
    p = 4
    c = c4+c5+c1+c8
}
one sig rule4 extends Rule{}{
    s =s0
    t =r8
    m = permission
    p = 3
    c = c3+c4+c1+c7+c5
}
one sig rule5 extends Rule{}{
    s =s2
    t =r2
    m = prohibition
    p = 1
    c = c4+c0+c2+c6
}
one sig rule6 extends Rule{}{
    s =s7
    t =r13
    m = prohibition
    p = 3
    c = c7+c1+c9+c4
}
one sig rule7 extends Rule{}{
    s =s10
    t =r21
    m = prohibition
    p = 0
    c = c6+c9+c1
}
one sig rule8 extends Rule{}{
    s =s14
    t =r1
    m = prohibition
    p = 1
    c = c3+c8+c5
}
one sig rule9 extends Rule{}{
    s =s12
    t =r20
    m = permission
    p = 3
    c = c0+c8+c2+c9+c4
}
one sig rule10 extends Rule{}{
    s =s6
    t =r9
    m = prohibition
    p = 3
    c = c9+c6+c7
}
one sig rule11 extends Rule{}{
    s =s20
    t =r1
    m = permission
    p = 3
    c = c1+c4+c2+c0
}
one sig rule12 extends Rule{}{
    s =s21
    t =r7
    m = permission
    p = 4
    c = c4+c8+c1+c3
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