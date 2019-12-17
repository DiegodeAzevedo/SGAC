module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s5->s1+
         s6->s0+
         s6->s1+
         s6->s4+
         s7->s2+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s6+
         s9->s8+
         s10->s3+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s1+
         s12->s5+
         s12->s6+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s9+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s6+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r10->r3+
         r10->r5+
         r10->r9+
         r11->r3+
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
         r13->r3+
         r13->r5+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r14+
         r16->r2+
         r16->r6+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r5
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r2
    m = permission
    p = 3
    c = c8
}
one sig rule1 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 2
    c = c7+c3+c0+c5+c1+c6
}
one sig rule2 extends Rule{}{
    s =s3
    t =r11
    m = prohibition
    p = 3
    c = c4+c0+c8
}
one sig rule3 extends Rule{}{
    s =s0
    t =r12
    m = prohibition
    p = 1
    c = c4+c7+c2+c0+c8
}
one sig rule4 extends Rule{}{
    s =s17
    t =r10
    m = permission
    p = 3
    c = c4+c0+c9+c1+c3
}
one sig rule5 extends Rule{}{
    s =s14
    t =r7
    m = prohibition
    p = 4
    c = c6+c3+c0+c5
}
one sig rule6 extends Rule{}{
    s =s10
    t =r4
    m = prohibition
    p = 1
    c = c4+c5+c9+c0
}
one sig rule7 extends Rule{}{
    s =s0
    t =r6
    m = prohibition
    p = 3
    c = c4+c3+c6+c8+c0+c7
}
one sig rule8 extends Rule{}{
    s =s12
    t =r5
    m = prohibition
    p = 4
    c = c9+c3+c2+c5+c1+c0
}
one sig rule9 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 2
    c = c6
}
one sig rule10 extends Rule{}{
    s =s2
    t =r9
    m = prohibition
    p = 3
    c = c0+c2+c9
}
one sig rule11 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 0
    c = c2+c8+c6+c4+c5
}
one sig rule12 extends Rule{}{
    s =s12
    t =r8
    m = permission
    p = 0
    c = c1+c6
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