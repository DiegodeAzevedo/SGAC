module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s3+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s7+
         s9->s8}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8 extends Resource{}{}
fact{
resSucc=r2->r1+
         r4->r1+
         r5->r1+
         r6->r0+
         r6->r2+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r6+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r0
    m = permission
    p = 4
    c = c8+c9
}
one sig rule1 extends Rule{}{
    s =s4
    t =r0
    m = permission
    p = 4
    c = c3
}
one sig rule2 extends Rule{}{
    s =s1
    t =r0
    m = permission
    p = 0
    c = c7+c0+c9+c6
}
one sig rule3 extends Rule{}{
    s =s6
    t =r3
    m = prohibition
    p = 0
    c = c4+c0+c3+c9
}
one sig rule4 extends Rule{}{
    s =s0
    t =r7
    m = permission
    p = 0
    c = c2+c6+c3+c8
}
one sig rule5 extends Rule{}{
    s =s1
    t =r1
    m = prohibition
    p = 2
    c = c2+c5
}
one sig rule6 extends Rule{}{
    s =s5
    t =r8
    m = permission
    p = 2
    c = c4+c1+c9
}
one sig rule7 extends Rule{}{
    s =s4
    t =r8
    m = permission
    p = 1
    c = c6
}
one sig rule8 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 3
    c = c2+c9+c6
}
one sig rule9 extends Rule{}{
    s =s6
    t =r1
    m = permission
    p = 2
    c = c7+c1+c8+c4+c0+c9
}
one sig rule10 extends Rule{}{
    s =s4
    t =r5
    m = permission
    p = 1
    c = c3+c1+c6+c8+c9+c7
}
one sig rule11 extends Rule{}{
    s =s0
    t =r3
    m = permission
    p = 3
    c = c2+c4+c7+c3+c8+c6
}
one sig rule12 extends Rule{}{
    s =s0
    t =r2
    m = permission
    p = 1
    c = c0+c2+c6
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
run grantingContextDetermination{grantingContextDet[req3]} for 4 but 1 GrantingContext