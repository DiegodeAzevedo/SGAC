module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s3+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s5+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s12+
         s14->s13}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r6+
         r9->r7+
         r10->r2+
         r10->r4+
         r10->r5+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r10+
         r12->r6+
         r12->r8+
         r12->r9+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r13}

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
    s =s8
    t =r2
    m = permission
    p = 3
    c = c5+c4+c7
}
one sig rule1 extends Rule{}{
    s =s14
    t =r3
    m = prohibition
    p = 0
    c = c6+c3+c7+c9
}
one sig rule2 extends Rule{}{
    s =s4
    t =r9
    m = prohibition
    p = 4
    c = c1
}
one sig rule3 extends Rule{}{
    s =s13
    t =r13
    m = prohibition
    p = 1
    c = c5+c9+c1+c3+c2+c0
}
one sig rule4 extends Rule{}{
    s =s2
    t =r2
    m = prohibition
    p = 1
    c = c5+c8+c9+c0+c1+c7
}
one sig rule5 extends Rule{}{
    s =s11
    t =r4
    m = permission
    p = 0
    c = c5+c6+c9+c4
}
one sig rule6 extends Rule{}{
    s =s0
    t =r4
    m = prohibition
    p = 0
    c = c2+c3
}
one sig rule7 extends Rule{}{
    s =s4
    t =r6
    m = permission
    p = 4
    c = c6+c0+c2+c1+c3
}
one sig rule8 extends Rule{}{
    s =s2
    t =r11
    m = prohibition
    p = 3
    c = c4
}
one sig rule9 extends Rule{}{
    s =s0
    t =r10
    m = prohibition
    p = 4
    c = c5+c1+c9+c4+c2+c6+c7
}
one sig rule10 extends Rule{}{
    s =s9
    t =r6
    m = permission
    p = 0
    c = c6+c8+c3+c1+c7+c9
}
one sig rule11 extends Rule{}{
    s =s1
    t =r11
    m = prohibition
    p = 0
    c = c7+c3
}
one sig rule12 extends Rule{}{
    s =s5
    t =r13
    m = permission
    p = 0
    c = c4
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