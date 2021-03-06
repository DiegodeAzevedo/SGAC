module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s5+
         s9->s0+
         s9->s4+
         s9->s6+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s2+
         s14->s7}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r4->r1+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r4+
         r8->r1+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r5+
         r10->r8+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r12->r0+
         r12->r6+
         r12->r7+
         r12->r10+
         r13->r2+
         r13->r3+
         r13->r6+
         r13->r9+
         r13->r10+
         r13->r12}

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
    s =s0
    t =r12
    m = prohibition
    p = 2
    c = c6+c8+c9+c1+c2
}
one sig rule1 extends Rule{}{
    s =s1
    t =r3
    m = prohibition
    p = 3
    c = c7+c9+c6+c2+c8
}
one sig rule2 extends Rule{}{
    s =s9
    t =r12
    m = prohibition
    p = 2
    c = c0+c5
}
one sig rule3 extends Rule{}{
    s =s13
    t =r11
    m = prohibition
    p = 1
    c = c7+c0+c3+c2+c8+c5+c6
}
one sig rule4 extends Rule{}{
    s =s2
    t =r12
    m = permission
    p = 2
    c = c4
}
one sig rule5 extends Rule{}{
    s =s1
    t =r13
    m = permission
    p = 4
    c = c6+c7+c1+c2+c3+c9
}
one sig rule6 extends Rule{}{
    s =s7
    t =r8
    m = prohibition
    p = 2
    c = c4
}
one sig rule7 extends Rule{}{
    s =s10
    t =r7
    m = permission
    p = 0
    c = c1+c6
}
one sig rule8 extends Rule{}{
    s =s11
    t =r2
    m = permission
    p = 4
    c = c4+c1+c3+c7+c9+c0
}
one sig rule9 extends Rule{}{
    s =s2
    t =r10
    m = prohibition
    p = 3
    c = c3+c1+c0+c2
}
one sig rule10 extends Rule{}{
    s =s7
    t =r7
    m = permission
    p = 2
    c = c8+c6
}
one sig rule11 extends Rule{}{
    s =s3
    t =r9
    m = permission
    p = 1
    c = c3+c9+c1
}
one sig rule12 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 3
    c = c8+c2+c5
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