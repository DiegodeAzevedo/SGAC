module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s3+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r10->r1+
         r10->r2+
         r10->r5+
         r10->r6+
         r10->r7}

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
    t =r4
    m = permission
    p = 2
    c = c2+c7+c5+c4+c9+c8
}
one sig rule1 extends Rule{}{
    s =s4
    t =r2
    m = prohibition
    p = 0
    c = c8+c9+c6+c7+c3+c0+c2
}
one sig rule2 extends Rule{}{
    s =s3
    t =r6
    m = prohibition
    p = 4
    c = c2+c6+c3
}
one sig rule3 extends Rule{}{
    s =s11
    t =r0
    m = prohibition
    p = 2
    c = c0+c6
}
one sig rule4 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 2
    c = c4+c1+c9+c8+c5+c6
}
one sig rule5 extends Rule{}{
    s =s8
    t =r3
    m = prohibition
    p = 1
    c = c2+c0+c3+c5
}
one sig rule6 extends Rule{}{
    s =s11
    t =r6
    m = permission
    p = 0
    c = c9+c5+c0+c7+c2+c1
}
one sig rule7 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 4
    c = c0+c3+c2+c8+c4+c1+c9
}
one sig rule8 extends Rule{}{
    s =s8
    t =r1
    m = permission
    p = 4
    c = c2+c0
}
one sig rule9 extends Rule{}{
    s =s11
    t =r7
    m = prohibition
    p = 1
    c = c2+c5+c7+c1+c9+c0+c8
}
one sig rule10 extends Rule{}{
    s =s1
    t =r2
    m = permission
    p = 3
    c = c0+c6+c1+c7+c3+c2
}
one sig rule11 extends Rule{}{
    s =s7
    t =r9
    m = prohibition
    p = 2
    c = c0+c4+c9+c1
}
one sig rule12 extends Rule{}{
    s =s6
    t =r8
    m = prohibition
    p = 4
    c = c4+c7+c2+c1+c5+c6
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