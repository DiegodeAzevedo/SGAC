module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s2+
         s4->s0+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s5+
         s8->s2}
one sig r0, r1, r2, r3, r4, r5, r6, r7 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r4}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r6
    m = prohibition
    p = 0
    c = c6+c8+c7+c1+c9+c3
}
one sig rule1 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 4
    c = c1
}
one sig rule2 extends Rule{}{
    s =s1
    t =r7
    m = prohibition
    p = 2
    c = c5+c8+c7
}
one sig rule3 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 2
    c = c1+c2+c5+c9+c0
}
one sig rule4 extends Rule{}{
    s =s1
    t =r3
    m = prohibition
    p = 2
    c = c9+c7+c2
}
one sig rule5 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 0
    c = c3+c7
}
one sig rule6 extends Rule{}{
    s =s5
    t =r2
    m = permission
    p = 0
    c = c6+c5+c9+c4+c2+c1
}
one sig rule7 extends Rule{}{
    s =s4
    t =r5
    m = permission
    p = 3
    c = c4+c2+c1+c7+c9+c0+c8+c6
}
one sig rule8 extends Rule{}{
    s =s4
    t =r6
    m = prohibition
    p = 4
    c = c5+c4
}
one sig rule9 extends Rule{}{
    s =s1
    t =r7
    m = permission
    p = 1
    c = c9+c5+c4+c2+c8+c0+c7
}
one sig rule10 extends Rule{}{
    s =s2
    t =r2
    m = prohibition
    p = 3
    c = c8
}
one sig rule11 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 4
    c = c5+c6+c8+c7+c9
}
one sig rule12 extends Rule{}{
    s =s8
    t =r0
    m = permission
    p = 3
    c = c2+c5+c0+c9+c7+c4+c6
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