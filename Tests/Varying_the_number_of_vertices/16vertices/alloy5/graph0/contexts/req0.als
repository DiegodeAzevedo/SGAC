module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s5->s1+
         s6->s0+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s5}
one sig r0, r1, r2, r3, r4, r5, r6, r7 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r3+
         r5->r0+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r3}

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
    t =r6
    m = permission
    p = 4
    c = c1+c7+c9+c3
}
one sig rule1 extends Rule{}{
    s =s6
    t =r5
    m = permission
    p = 4
    c = c2+c9+c5+c1+c7+c6+c3
}
one sig rule2 extends Rule{}{
    s =s1
    t =r2
    m = prohibition
    p = 2
    c = c5+c8+c0
}
one sig rule3 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 2
    c = c8+c6+c9+c0+c5+c1+c4+c7
}
one sig rule4 extends Rule{}{
    s =s6
    t =r3
    m = permission
    p = 1
    c = c4+c8+c1+c9
}
one sig rule5 extends Rule{}{
    s =s4
    t =r6
    m = permission
    p = 2
    c = c5+c2
}
one sig rule6 extends Rule{}{
    s =s2
    t =r4
    m = permission
    p = 1
    c = c6+c4+c9+c2+c5+c7
}
one sig rule7 extends Rule{}{
    s =s5
    t =r1
    m = permission
    p = 3
    c = c5+c1+c3+c2+c7
}
one sig rule8 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 3
    c = c5
}
one sig rule9 extends Rule{}{
    s =s0
    t =r0
    m = permission
    p = 0
    c = c5+c3+c1+c0+c2
}
one sig rule10 extends Rule{}{
    s =s2
    t =r2
    m = permission
    p = 4
    c = c2+c1+c4+c3+c6+c5
}
one sig rule11 extends Rule{}{
    s =s7
    t =r3
    m = permission
    p = 3
    c = c9+c7+c6+c0+c2
}
one sig rule12 extends Rule{}{
    s =s5
    t =r4
    m = permission
    p = 4
    c = c8+c4+c6+c7+c3
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