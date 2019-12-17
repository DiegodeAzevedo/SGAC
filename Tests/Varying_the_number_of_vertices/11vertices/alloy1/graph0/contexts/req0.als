module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s4->s3+
         s5->s2+
         s5->s3+
         s5->s4}
one sig r0, r1, r2, r3, r4 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3}

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
    s =s5
    t =r1
    m = permission
    p = 4
    c = c3+c0+c9+c7+c5
}
one sig rule1 extends Rule{}{
    s =s5
    t =r2
    m = prohibition
    p = 0
    c = c3+c6+c8+c2+c1+c4
}
one sig rule2 extends Rule{}{
    s =s0
    t =r2
    m = prohibition
    p = 0
    c = c0+c2+c5+c6+c1+c4
}
one sig rule3 extends Rule{}{
    s =s5
    t =r2
    m = permission
    p = 3
    c = c2+c6+c8+c3+c1
}
one sig rule4 extends Rule{}{
    s =s5
    t =r3
    m = prohibition
    p = 3
    c = c7+c6+c3+c9+c0+c8
}
one sig rule5 extends Rule{}{
    s =s2
    t =r2
    m = prohibition
    p = 3
    c = c7+c2+c0+c5+c3+c8
}
one sig rule6 extends Rule{}{
    s =s0
    t =r3
    m = prohibition
    p = 3
    c = c9+c4+c5+c1+c8
}
one sig rule7 extends Rule{}{
    s =s0
    t =r2
    m = permission
    p = 3
    c = c8
}
one sig rule8 extends Rule{}{
    s =s1
    t =r1
    m = prohibition
    p = 4
    c = c6+c3+c0+c7
}
one sig rule9 extends Rule{}{
    s =s4
    t =r3
    m = permission
    p = 2
    c = c2+c7+c8+c4+c1+c5
}
one sig rule10 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 0
    c = c0+c5
}
one sig rule11 extends Rule{}{
    s =s4
    t =r0
    m = prohibition
    p = 2
    c = c7+c5+c3+c6+c4
}
one sig rule12 extends Rule{}{
    s =s4
    t =r4
    m = prohibition
    p = 1
    c = c5+c3+c9+c4
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