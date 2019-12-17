module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s5->s0+
         s5->s2+
         s6->s2+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s7+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s8+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s7+
         s15->s10+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s14+
         s18->s17+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s13+
         s19->s14+
         s19->s16+
         s20->s4+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s18+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s7+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s12+
         s22->s14+
         s22->s20+
         s22->s21+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s21+
         s24->s22+
         s24->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r0+
         r4->r1+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r9+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r7+
         r15->r8+
         r15->r14+
         r16->r3+
         r16->r5+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r14+
         r18->r15+
         r19->r1+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r12+
         r19->r14+
         r20->r1+
         r20->r2+
         r20->r6+
         r20->r8+
         r20->r10+
         r20->r17+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r10+
         r21->r13+
         r21->r20+
         r22->r2+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r21+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r6+
         r23->r9+
         r23->r11+
         r23->r12+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r6+
         r24->r7+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r17+
         r24->r19+
         r24->r20}

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
    s =s5
    t =r7
    m = prohibition
    p = 3
    c = c9+c4+c0
}
one sig rule1 extends Rule{}{
    s =s19
    t =r4
    m = prohibition
    p = 3
    c = c1+c8+c0+c9+c4+c2
}
one sig rule2 extends Rule{}{
    s =s6
    t =r20
    m = permission
    p = 4
    c = c8+c4+c5+c6+c7+c0+c3+c1
}
one sig rule3 extends Rule{}{
    s =s12
    t =r23
    m = permission
    p = 2
    c = c2+c9+c7+c3+c4
}
one sig rule4 extends Rule{}{
    s =s24
    t =r21
    m = prohibition
    p = 2
    c = c9+c1+c7+c5
}
one sig rule5 extends Rule{}{
    s =s14
    t =r24
    m = permission
    p = 4
    c = c7+c0+c5
}
one sig rule6 extends Rule{}{
    s =s14
    t =r13
    m = permission
    p = 2
    c = c0+c3+c2+c5+c8+c4
}
one sig rule7 extends Rule{}{
    s =s21
    t =r0
    m = prohibition
    p = 2
    c = c6+c4+c0
}
one sig rule8 extends Rule{}{
    s =s12
    t =r24
    m = prohibition
    p = 0
    c = c6
}
one sig rule9 extends Rule{}{
    s =s22
    t =r19
    m = permission
    p = 4
    c = c0+c4+c5+c8+c6+c3
}
one sig rule10 extends Rule{}{
    s =s20
    t =r6
    m = permission
    p = 2
    c = c8+c0+c5
}
one sig rule11 extends Rule{}{
    s =s0
    t =r14
    m = permission
    p = 1
    c = c9+c8+c6+c7
}
one sig rule12 extends Rule{}{
    s =s3
    t =r24
    m = prohibition
    p = 1
    c = c3+c4+c9+c0+c7
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