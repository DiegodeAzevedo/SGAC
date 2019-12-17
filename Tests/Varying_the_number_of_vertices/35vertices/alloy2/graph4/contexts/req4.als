module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17 extends Subject{}{}
fact{
subSucc=s3->s1+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s5+
         s9->s3+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s8+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s10+
         s13->s0+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s7+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s6+
         s17->s7+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r5+
         r9->r8+
         r10->r2+
         r10->r5+
         r10->r8+
         r11->r1+
         r11->r3+
         r11->r7+
         r12->r2+
         r12->r10+
         r13->r2+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r4+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r6+
         r15->r7+
         r15->r12+
         r16->r0+
         r16->r4+
         r16->r8+
         r16->r11+
         r16->r12+
         r16->r13}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r15
    m = prohibition
    p = 3
    c = c8+c6
}
one sig rule1 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 4
    c = c5
}
one sig rule2 extends Rule{}{
    s =s9
    t =r6
    m = permission
    p = 2
    c = c4+c0
}
one sig rule3 extends Rule{}{
    s =s17
    t =r3
    m = prohibition
    p = 1
    c = c2+c8+c4+c9+c5+c1
}
one sig rule4 extends Rule{}{
    s =s9
    t =r9
    m = permission
    p = 0
    c = c8+c9
}
one sig rule5 extends Rule{}{
    s =s13
    t =r3
    m = permission
    p = 2
    c = c5+c2+c9+c6+c3+c8+c1+c0
}
one sig rule6 extends Rule{}{
    s =s3
    t =r12
    m = permission
    p = 2
    c = c5+c8+c4+c9
}
one sig rule7 extends Rule{}{
    s =s13
    t =r3
    m = prohibition
    p = 0
    c = c7+c5+c2
}
one sig rule8 extends Rule{}{
    s =s9
    t =r8
    m = prohibition
    p = 1
    c = c0+c5+c1+c4
}
one sig rule9 extends Rule{}{
    s =s15
    t =r3
    m = permission
    p = 4
    c = c8+c6+c5+c2+c9
}
one sig rule10 extends Rule{}{
    s =s15
    t =r3
    m = permission
    p = 2
    c = c6+c3
}
one sig rule11 extends Rule{}{
    s =s9
    t =r12
    m = prohibition
    p = 1
    c = c8+c0+c9+c1+c6
}
one sig rule12 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 4
    c = c7+c9+c3+c0+c2+c1+c6
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
run grantingContextDetermination{grantingContextDet[req4]} for 4 but 1 GrantingContext