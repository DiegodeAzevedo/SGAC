module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s6+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s5+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s2+
         s13->s3+
         s13->s5+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s9+
         s15->s1+
         s15->s3+
         s15->s6+
         s15->s9+
         s15->s11+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s10+
         s17->s14+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r4->r1+
         r5->r0+
         r5->r2+
         r5->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r6+
         r9->r7+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r2+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r6+
         r14->r8+
         r14->r13+
         r15->r1+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r2+
         r17->r5+
         r17->r8+
         r17->r13+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r18
    m = prohibition
    p = 1
    c = c0+c1+c9+c6+c4+c8
}
one sig rule1 extends Rule{}{
    s =s17
    t =r14
    m = permission
    p = 2
    c = c4+c8+c7+c5+c3
}
one sig rule2 extends Rule{}{
    s =s19
    t =r6
    m = prohibition
    p = 0
    c = c9+c1+c3+c6
}
one sig rule3 extends Rule{}{
    s =s12
    t =r7
    m = permission
    p = 1
    c = c6+c3+c7+c1+c2
}
one sig rule4 extends Rule{}{
    s =s15
    t =r3
    m = prohibition
    p = 0
    c = c9+c6+c2+c7
}
one sig rule5 extends Rule{}{
    s =s17
    t =r7
    m = prohibition
    p = 2
    c = c6+c0+c7+c1+c5+c3
}
one sig rule6 extends Rule{}{
    s =s9
    t =r12
    m = prohibition
    p = 1
    c = c7+c4+c2+c1
}
one sig rule7 extends Rule{}{
    s =s12
    t =r7
    m = permission
    p = 3
    c = c8+c1+c4+c9
}
one sig rule8 extends Rule{}{
    s =s3
    t =r2
    m = prohibition
    p = 3
    c = c0+c3+c1
}
one sig rule9 extends Rule{}{
    s =s11
    t =r10
    m = permission
    p = 2
    c = c6
}
one sig rule10 extends Rule{}{
    s =s8
    t =r5
    m = permission
    p = 1
    c = c1+c6
}
one sig rule11 extends Rule{}{
    s =s13
    t =r4
    m = permission
    p = 2
    c = c4+c1+c7+c6+c5+c9+c3+c2
}
one sig rule12 extends Rule{}{
    s =s15
    t =r19
    m = permission
    p = 2
    c = c6+c5+c4+c0
}
one sig rule13 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 2
    c = c6
}
one sig rule14 extends Rule{}{
    s =s7
    t =r11
    m = prohibition
    p = 2
    c = c3
}
one sig rule15 extends Rule{}{
    s =s19
    t =r7
    m = permission
    p = 0
    c = c2+c8
}
one sig rule16 extends Rule{}{
    s =s10
    t =r9
    m = prohibition
    p = 2
    c = c7+c4+c6
}
one sig rule17 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 0
    c = c7+c9+c5+c1+c6
}
one sig rule18 extends Rule{}{
    s =s6
    t =r14
    m = prohibition
    p = 4
    c = c3
}
one sig rule19 extends Rule{}{
    s =s15
    t =r17
    m = prohibition
    p = 3
    c = c8+c6
}
one sig rule20 extends Rule{}{
    s =s3
    t =r13
    m = prohibition
    p = 0
    c = c2+c7+c9+c4+c3+c5+c6
}
one sig rule21 extends Rule{}{
    s =s6
    t =r12
    m = prohibition
    p = 0
    c = c2+c3+c4+c0
}
one sig rule22 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 4
    c = c4+c2+c6
}
one sig rule23 extends Rule{}{
    s =s12
    t =r2
    m = permission
    p = 4
    c = c5+c6
}
one sig rule24 extends Rule{}{
    s =s7
    t =r17
    m = prohibition
    p = 0
    c = c7+c2+c1+c0+c9+c4+c5
}
one sig rule25 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 4
    c = c9
}
one sig rule26 extends Rule{}{
    s =s7
    t =r4
    m = permission
    p = 1
    c = c0
}
one sig rule27 extends Rule{}{
    s =s4
    t =r15
    m = prohibition
    p = 0
    c = c1+c4+c9+c3+c0+c5+c7
}
one sig rule28 extends Rule{}{
    s =s4
    t =r0
    m = prohibition
    p = 4
    c = c5+c9+c3+c0+c4
}
one sig rule29 extends Rule{}{
    s =s17
    t =r6
    m = permission
    p = 4
    c = c1
}
one sig rule30 extends Rule{}{
    s =s4
    t =r8
    m = prohibition
    p = 3
    c = c5+c0
}
one sig rule31 extends Rule{}{
    s =s6
    t =r13
    m = prohibition
    p = 0
    c = c0
}
one sig rule32 extends Rule{}{
    s =s5
    t =r19
    m = permission
    p = 1
    c = c2+c4+c0+c8+c3
}
one sig rule33 extends Rule{}{
    s =s0
    t =r2
    m = prohibition
    p = 3
    c = c8+c3+c2+c0+c5+c7
}
one sig rule34 extends Rule{}{
    s =s12
    t =r7
    m = prohibition
    p = 4
    c = c6+c1+c9+c5
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