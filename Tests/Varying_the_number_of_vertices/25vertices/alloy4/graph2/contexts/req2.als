module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s5->s2+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s0+
         s8->s2+
         s8->s4+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s5+
         s11->s0+
         s11->s5+
         s11->s8+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s8+
         s12->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r1+
         r9->r3+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r7+
         r11->r8+
         r11->r10}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s0
    t =r11
    m = permission
    p = 1
    c = c5+c3+c0
}
one sig rule1 extends Rule{}{
    s =s0
    t =r3
    m = permission
    p = 0
    c = c1+c3+c9
}
one sig rule2 extends Rule{}{
    s =s12
    t =r7
    m = permission
    p = 4
    c = c4+c5+c9+c0+c6+c2
}
one sig rule3 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 1
    c = c0+c9+c4+c2+c7+c3+c1
}
one sig rule4 extends Rule{}{
    s =s12
    t =r4
    m = prohibition
    p = 2
    c = c1+c9+c4+c2+c8+c5
}
one sig rule5 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 0
    c = c7+c1+c8+c5
}
one sig rule6 extends Rule{}{
    s =s3
    t =r10
    m = permission
    p = 1
    c = c3
}
one sig rule7 extends Rule{}{
    s =s2
    t =r11
    m = prohibition
    p = 1
    c = c7+c8+c3+c2+c9+c4+c0+c1
}
one sig rule8 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 0
    c = c7
}
one sig rule9 extends Rule{}{
    s =s10
    t =r7
    m = permission
    p = 3
    c = c5+c4+c7
}
one sig rule10 extends Rule{}{
    s =s4
    t =r3
    m = prohibition
    p = 4
    c = c8+c6+c0
}
one sig rule11 extends Rule{}{
    s =s6
    t =r5
    m = permission
    p = 0
    c = c3+c5+c4+c2+c6
}
one sig rule12 extends Rule{}{
    s =s12
    t =r10
    m = permission
    p = 1
    c = c5+c9+c2+c6
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