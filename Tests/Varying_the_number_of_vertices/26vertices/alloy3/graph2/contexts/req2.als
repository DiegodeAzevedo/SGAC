module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s2+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s3+
         s10->s7+
         s11->s0+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s9+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r4+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r10+
         r12->r0+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s4
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r9
    m = permission
    p = 1
    c = c0+c8+c2+c1+c4+c3
}
one sig rule1 extends Rule{}{
    s =s12
    t =r6
    m = permission
    p = 1
    c = c3+c4+c8+c2+c9
}
one sig rule2 extends Rule{}{
    s =s1
    t =r6
    m = prohibition
    p = 3
    c = c3+c4+c5
}
one sig rule3 extends Rule{}{
    s =s8
    t =r10
    m = prohibition
    p = 0
    c = c4+c0+c5+c2+c9+c3
}
one sig rule4 extends Rule{}{
    s =s3
    t =r4
    m = prohibition
    p = 0
    c = c4+c1+c5+c8
}
one sig rule5 extends Rule{}{
    s =s10
    t =r2
    m = prohibition
    p = 0
    c = c2+c8+c4+c7+c1+c3
}
one sig rule6 extends Rule{}{
    s =s4
    t =r8
    m = permission
    p = 4
    c = c9+c4+c6+c8+c0+c5+c2
}
one sig rule7 extends Rule{}{
    s =s1
    t =r8
    m = prohibition
    p = 3
    c = c0+c1+c9+c5+c4+c2+c8
}
one sig rule8 extends Rule{}{
    s =s9
    t =r10
    m = permission
    p = 1
    c = c6+c5+c9+c2+c7+c0
}
one sig rule9 extends Rule{}{
    s =s10
    t =r4
    m = prohibition
    p = 0
    c = c8+c6
}
one sig rule10 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 2
    c = c1+c3+c2+c8
}
one sig rule11 extends Rule{}{
    s =s4
    t =r7
    m = prohibition
    p = 1
    c = c8+c4
}
one sig rule12 extends Rule{}{
    s =s3
    t =r11
    m = prohibition
    p = 4
    c = c4+c0+c5+c9+c6+c3
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