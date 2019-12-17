module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s0+
         s5->s2+
         s5->s4}
one sig r0, r1, r2, r3, r4, r5 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r3+
         r5->r4}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r4
    m = prohibition
    p = 1
    c = c1+c5+c7+c6+c4
}
one sig rule1 extends Rule{}{
    s =s0
    t =r5
    m = prohibition
    p = 3
    c = c1+c6+c4
}
one sig rule2 extends Rule{}{
    s =s1
    t =r1
    m = prohibition
    p = 4
    c = c7+c3+c9+c2+c8
}
one sig rule3 extends Rule{}{
    s =s3
    t =r2
    m = prohibition
    p = 0
    c = c8+c5+c2
}
one sig rule4 extends Rule{}{
    s =s1
    t =r1
    m = prohibition
    p = 0
    c = c8+c1+c4+c7
}
one sig rule5 extends Rule{}{
    s =s3
    t =r4
    m = permission
    p = 1
    c = c0+c7+c6+c3
}
one sig rule6 extends Rule{}{
    s =s4
    t =r5
    m = prohibition
    p = 2
    c = c5+c4+c3+c6
}
one sig rule7 extends Rule{}{
    s =s3
    t =r0
    m = permission
    p = 3
    c = c2
}
one sig rule8 extends Rule{}{
    s =s0
    t =r3
    m = permission
    p = 4
    c = c7+c2
}
one sig rule9 extends Rule{}{
    s =s1
    t =r3
    m = prohibition
    p = 3
    c = c8+c9+c0+c2+c6+c1
}
one sig rule10 extends Rule{}{
    s =s1
    t =r4
    m = prohibition
    p = 4
    c = c0+c2+c7+c5+c6
}
one sig rule11 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 2
    c = c8+c2+c0+c4+c1+c5
}
one sig rule12 extends Rule{}{
    s =s0
    t =r3
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
run grantingContextDetermination{grantingContextDet[req3]} for 4 but 1 GrantingContext