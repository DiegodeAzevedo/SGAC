module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s7->s6}
one sig r0, r1, r2, r3, r4, r5, r6 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r4->r0+
         r4->r2+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r2
    m = permission
    p = 0
    c = c5+c7+c9+c0+c1
}
one sig rule1 extends Rule{}{
    s =s6
    t =r0
    m = prohibition
    p = 0
    c = c4+c5+c8+c6
}
one sig rule2 extends Rule{}{
    s =s0
    t =r5
    m = permission
    p = 2
    c = c8+c9
}
one sig rule3 extends Rule{}{
    s =s3
    t =r4
    m = prohibition
    p = 1
    c = c1+c5+c3+c0+c2
}
one sig rule4 extends Rule{}{
    s =s6
    t =r3
    m = permission
    p = 4
    c = c4+c2+c6
}
one sig rule5 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 4
    c = c6+c4+c9+c5+c1+c2+c8
}
one sig rule6 extends Rule{}{
    s =s1
    t =r4
    m = prohibition
    p = 4
    c = c0+c4+c5+c2
}
one sig rule7 extends Rule{}{
    s =s4
    t =r4
    m = prohibition
    p = 4
    c = c4+c8+c9+c0
}
one sig rule8 extends Rule{}{
    s =s1
    t =r6
    m = prohibition
    p = 4
    c = c8+c0
}
one sig rule9 extends Rule{}{
    s =s6
    t =r1
    m = prohibition
    p = 4
    c = c8+c3+c5+c7
}
one sig rule10 extends Rule{}{
    s =s5
    t =r1
    m = prohibition
    p = 3
    c = c6+c0+c5+c3+c7+c8+c1
}
one sig rule11 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 4
    c = c0+c2+c9+c4+c5
}
one sig rule12 extends Rule{}{
    s =s4
    t =r2
    m = prohibition
    p = 2
    c = c7+c6+c0+c4+c5
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
run grantingContextDetermination{grantingContextDet[req2]} for 4 but 1 GrantingContext