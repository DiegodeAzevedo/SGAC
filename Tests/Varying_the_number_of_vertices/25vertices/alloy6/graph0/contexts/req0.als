module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12 extends Subject{}{}
fact{
subSucc=s3->s1+
         s4->s0+
         s4->s2+
         s5->s4+
         s6->s0+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s3+
         s9->s4+
         s9->s6+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s8+
         s11->s5+
         s11->s6+
         s11->s8+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s10+
         s12->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r9}

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
    s =s1
    t =r2
    m = prohibition
    p = 2
    c = c6+c8+c4+c7
}
one sig rule1 extends Rule{}{
    s =s12
    t =r9
    m = prohibition
    p = 1
    c = c4+c2+c6+c9+c8
}
one sig rule2 extends Rule{}{
    s =s11
    t =r7
    m = permission
    p = 2
    c = c4+c1+c2+c3+c0+c9+c6+c8
}
one sig rule3 extends Rule{}{
    s =s7
    t =r1
    m = permission
    p = 4
    c = c8+c0
}
one sig rule4 extends Rule{}{
    s =s0
    t =r3
    m = permission
    p = 3
    c = c9
}
one sig rule5 extends Rule{}{
    s =s9
    t =r5
    m = prohibition
    p = 3
    c = c1+c4+c6+c9
}
one sig rule6 extends Rule{}{
    s =s11
    t =r11
    m = prohibition
    p = 2
    c = c1+c0+c5+c8+c2+c6
}
one sig rule7 extends Rule{}{
    s =s9
    t =r1
    m = prohibition
    p = 1
    c = c3+c4+c9
}
one sig rule8 extends Rule{}{
    s =s6
    t =r10
    m = prohibition
    p = 4
    c = c6+c8+c0+c9+c4+c3
}
one sig rule9 extends Rule{}{
    s =s11
    t =r3
    m = prohibition
    p = 4
    c = c2+c3+c6+c0+c4+c9
}
one sig rule10 extends Rule{}{
    s =s4
    t =r5
    m = permission
    p = 0
    c = c7+c9+c0
}
one sig rule11 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 2
    c = c5+c4
}
one sig rule12 extends Rule{}{
    s =s8
    t =r6
    m = permission
    p = 0
    c = c5+c0+c1+c4
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