module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s2+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s4+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s7+
         s12->s0+
         s12->s1+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r2+
         r4->r2+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r3+
         r7->r0+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r3+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r11->r2+
         r11->r6+
         r11->r9}

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
    s =s3
    t =r1
    m = permission
    p = 2
    c = c3+c6+c5+c8
}
one sig rule1 extends Rule{}{
    s =s6
    t =r10
    m = prohibition
    p = 3
    c = c5+c9+c8+c7
}
one sig rule2 extends Rule{}{
    s =s8
    t =r6
    m = permission
    p = 4
    c = c4+c3
}
one sig rule3 extends Rule{}{
    s =s5
    t =r3
    m = permission
    p = 0
    c = c6+c5+c1+c8+c9
}
one sig rule4 extends Rule{}{
    s =s9
    t =r8
    m = permission
    p = 0
    c = c0+c1+c2+c6+c3+c9
}
one sig rule5 extends Rule{}{
    s =s3
    t =r4
    m = permission
    p = 2
    c = c8+c5+c3+c4+c1+c0+c9
}
one sig rule6 extends Rule{}{
    s =s8
    t =r7
    m = permission
    p = 4
    c = c1+c6+c8+c2+c4
}
one sig rule7 extends Rule{}{
    s =s2
    t =r9
    m = prohibition
    p = 1
    c = c3+c6+c1+c4
}
one sig rule8 extends Rule{}{
    s =s8
    t =r9
    m = prohibition
    p = 1
    c = c3+c2+c6+c5+c4
}
one sig rule9 extends Rule{}{
    s =s10
    t =r4
    m = prohibition
    p = 4
    c = c0+c8+c7
}
one sig rule10 extends Rule{}{
    s =s10
    t =r5
    m = prohibition
    p = 0
    c = c9+c6+c4+c5+c0+c3
}
one sig rule11 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 0
    c = c1+c7+c9+c2
}
one sig rule12 extends Rule{}{
    s =s1
    t =r6
    m = permission
    p = 0
    c = c4+c8+c7+c9
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