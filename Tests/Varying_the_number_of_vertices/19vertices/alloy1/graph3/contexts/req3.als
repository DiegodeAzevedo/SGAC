module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s5}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r2+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r3+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r6}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s3
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r5
    m = prohibition
    p = 1
    c = c9+c2+c5+c7+c4+c8
}
one sig rule1 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 2
    c = c1+c3+c5+c0+c7+c8
}
one sig rule2 extends Rule{}{
    s =s9
    t =r8
    m = prohibition
    p = 0
    c = c6+c3+c7+c8
}
one sig rule3 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 0
    c = c2+c4+c6+c7+c0+c9
}
one sig rule4 extends Rule{}{
    s =s4
    t =r4
    m = permission
    p = 1
    c = c6+c1+c3
}
one sig rule5 extends Rule{}{
    s =s8
    t =r2
    m = prohibition
    p = 3
    c = c6
}
one sig rule6 extends Rule{}{
    s =s8
    t =r4
    m = permission
    p = 1
    c = c0+c3+c6+c8+c1+c2+c5
}
one sig rule7 extends Rule{}{
    s =s9
    t =r7
    m = prohibition
    p = 4
    c = c5+c8+c2
}
one sig rule8 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 3
    c = c6+c9+c4+c0+c1+c8+c5
}
one sig rule9 extends Rule{}{
    s =s8
    t =r8
    m = prohibition
    p = 0
    c = c7
}
one sig rule10 extends Rule{}{
    s =s9
    t =r5
    m = permission
    p = 0
    c = c5
}
one sig rule11 extends Rule{}{
    s =s6
    t =r7
    m = permission
    p = 1
    c = c4+c2+c0+c6
}
one sig rule12 extends Rule{}{
    s =s9
    t =r5
    m = prohibition
    p = 3
    c = c1+c7
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