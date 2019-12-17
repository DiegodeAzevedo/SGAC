module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s5+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s9+
         s13->s10+
         s13->s12}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r2+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r1+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r5+
         r10->r6+
         r11->r0+
         r11->r3+
         r11->r5+
         r11->r9+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r10+
         r12->r11}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

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
    s =s5
    t =r0
    m = permission
    p = 0
    c = c2+c0+c4+c5
}
one sig rule1 extends Rule{}{
    s =s7
    t =r8
    m = permission
    p = 3
    c = c0+c9+c7+c6+c5+c2+c1
}
one sig rule2 extends Rule{}{
    s =s5
    t =r3
    m = permission
    p = 4
    c = c9+c8+c5+c4+c3+c6+c0
}
one sig rule3 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 2
    c = c2+c1+c9+c0+c8+c4+c6
}
one sig rule4 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 0
    c = c5+c1+c7+c2+c8+c4+c6+c0
}
one sig rule5 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 1
    c = c0+c5+c7+c9+c4+c8+c6+c2
}
one sig rule6 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 2
    c = c5+c8+c3+c0+c2+c1+c6+c7
}
one sig rule7 extends Rule{}{
    s =s12
    t =r8
    m = prohibition
    p = 3
    c = c2+c1+c7+c8+c5+c9
}
one sig rule8 extends Rule{}{
    s =s0
    t =r10
    m = prohibition
    p = 3
    c = c5
}
one sig rule9 extends Rule{}{
    s =s11
    t =r0
    m = permission
    p = 2
    c = c8+c0
}
one sig rule10 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 2
    c = c8
}
one sig rule11 extends Rule{}{
    s =s6
    t =r3
    m = permission
    p = 2
    c = c1+c6
}
one sig rule12 extends Rule{}{
    s =s5
    t =r4
    m = permission
    p = 3
    c = c1
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