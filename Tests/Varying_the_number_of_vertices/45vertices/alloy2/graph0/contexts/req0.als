module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s2+
         s7->s0+
         s7->s3+
         s7->s4+
         s8->s1+
         s8->s5+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s5+
         s11->s0+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s11+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s4+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s4+
         s19->s6+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s7+
         s20->s9+
         s20->s17+
         s20->s19+
         s21->s6+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s17+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s16+
         s22->s18+
         s22->s19+
         s22->s21}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r2+
         r6->r1+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r2+
         r8->r7+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r2+
         r10->r3+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r7+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r11+
         r13->r0+
         r13->r2+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r9+
         r14->r11+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r9+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r6+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r8+
         r17->r9+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r7+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r1+
         r20->r4+
         r20->r5+
         r20->r7+
         r20->r10+
         r20->r11+
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
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r13+
         r21->r16+
         r21->r17}

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
    s =s1
    t =r21
    m = prohibition
    p = 3
    c = c1
}
one sig rule1 extends Rule{}{
    s =s0
    t =r21
    m = permission
    p = 0
    c = c3+c7+c9
}
one sig rule2 extends Rule{}{
    s =s5
    t =r12
    m = prohibition
    p = 2
    c = c4+c6+c3+c1+c8
}
one sig rule3 extends Rule{}{
    s =s20
    t =r18
    m = prohibition
    p = 2
    c = c1+c4+c7+c9+c5+c2+c0
}
one sig rule4 extends Rule{}{
    s =s5
    t =r16
    m = permission
    p = 1
    c = c7+c1+c0
}
one sig rule5 extends Rule{}{
    s =s11
    t =r17
    m = permission
    p = 3
    c = c4+c7+c5+c6+c2+c1+c3+c0
}
one sig rule6 extends Rule{}{
    s =s20
    t =r18
    m = permission
    p = 2
    c = c2+c9+c8+c6+c4
}
one sig rule7 extends Rule{}{
    s =s4
    t =r15
    m = prohibition
    p = 3
    c = c9+c3+c7+c0
}
one sig rule8 extends Rule{}{
    s =s18
    t =r1
    m = prohibition
    p = 4
    c = c5+c9+c8+c4+c1
}
one sig rule9 extends Rule{}{
    s =s2
    t =r20
    m = permission
    p = 2
    c = c3+c4+c0
}
one sig rule10 extends Rule{}{
    s =s11
    t =r15
    m = prohibition
    p = 3
    c = c5+c1+c9+c8+c4
}
one sig rule11 extends Rule{}{
    s =s12
    t =r0
    m = prohibition
    p = 2
    c = c2+c6+c7
}
one sig rule12 extends Rule{}{
    s =s21
    t =r18
    m = prohibition
    p = 2
    c = c6+c5+c2
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