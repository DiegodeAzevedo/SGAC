module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s5+
         s7->s2+
         s7->s3+
         s7->s5}
one sig r0, r1, r2, r3, r4, r5, r6 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r2+
         r4->r3+
         r6->r0+
         r6->r1}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r5
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r1
    m = permission
    p = 3
    c = c3+c1
}
one sig rule1 extends Rule{}{
    s =s0
    t =r3
    m = prohibition
    p = 2
    c = c9+c0+c5
}
one sig rule2 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 4
    c = c0+c8
}
one sig rule3 extends Rule{}{
    s =s0
    t =r1
    m = permission
    p = 2
    c = c9+c7
}
one sig rule4 extends Rule{}{
    s =s4
    t =r4
    m = permission
    p = 0
    c = c9+c0+c8
}
one sig rule5 extends Rule{}{
    s =s1
    t =r1
    m = permission
    p = 1
    c = c2+c6+c7
}
one sig rule6 extends Rule{}{
    s =s1
    t =r5
    m = prohibition
    p = 0
    c = c7+c8+c9+c6
}
one sig rule7 extends Rule{}{
    s =s4
    t =r4
    m = prohibition
    p = 0
    c = c4+c9+c7
}
one sig rule8 extends Rule{}{
    s =s1
    t =r0
    m = prohibition
    p = 2
    c = c3+c1+c7+c0+c8+c5+c2
}
one sig rule9 extends Rule{}{
    s =s2
    t =r5
    m = permission
    p = 2
    c = c9+c0+c5+c2+c6
}
one sig rule10 extends Rule{}{
    s =s2
    t =r5
    m = prohibition
    p = 2
    c = c0+c8+c7+c2+c9
}
one sig rule11 extends Rule{}{
    s =s3
    t =r1
    m = permission
    p = 1
    c = c8+c6+c9
}
one sig rule12 extends Rule{}{
    s =s7
    t =r5
    m = permission
    p = 0
    c = c3+c1
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