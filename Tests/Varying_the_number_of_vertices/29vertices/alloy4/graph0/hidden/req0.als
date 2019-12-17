module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14 extends Subject{}{}
fact{
subSucc=s2->s1+
         s4->s1+
         s5->s0+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s4+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s1+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s10+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s8+
         s12->s11+
         s13->s1+
         s13->s6+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s11}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r2+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r4+
         r7->r5+
         r8->r3+
         r8->r4+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r6+
         r10->r0+
         r10->r2+
         r10->r5+
         r10->r7+
         r10->r8+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r12}

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
    s =s13
    t =r12
    m = permission
    p = 4
    c = c1+c2+c0+c9+c3
}
one sig rule1 extends Rule{}{
    s =s9
    t =r4
    m = prohibition
    p = 1
    c = c3+c0+c4+c5
}
one sig rule2 extends Rule{}{
    s =s10
    t =r0
    m = prohibition
    p = 3
    c = c8+c7
}
one sig rule3 extends Rule{}{
    s =s14
    t =r7
    m = prohibition
    p = 3
    c = c2+c3+c5+c9+c8+c6
}
one sig rule4 extends Rule{}{
    s =s3
    t =r7
    m = prohibition
    p = 2
    c = c0+c1+c6+c2
}
one sig rule5 extends Rule{}{
    s =s12
    t =r0
    m = prohibition
    p = 0
    c = c3+c9+c6+c8
}
one sig rule6 extends Rule{}{
    s =s2
    t =r8
    m = prohibition
    p = 0
    c = c5+c8+c1+c0+c6+c4
}
one sig rule7 extends Rule{}{
    s =s4
    t =r11
    m = permission
    p = 2
    c = c4+c8+c3+c1
}
one sig rule8 extends Rule{}{
    s =s2
    t =r9
    m = prohibition
    p = 2
    c = c0+c2+c4+c9+c8+c6
}
one sig rule9 extends Rule{}{
    s =s12
    t =r13
    m = prohibition
    p = 2
    c = c1+c7
}
one sig rule10 extends Rule{}{
    s =s9
    t =r8
    m = permission
    p = 3
    c = c1+c8+c0+c2+c7
}
one sig rule11 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 2
    c = c9
}
one sig rule12 extends Rule{}{
    s =s14
    t =r13
    m = permission
    p = 0
    c = c1+c4+c2+c7+c3
}
//**************************
//***Auxiliary Predicates***
//**************************
pred access_condition[req:Request,con:Context]{
    (no  r:applicableRules[req] |  (evalRuleCond[r,con] and r.m=prohibition and
        all rule: r.^(req.ruleSucc) | not evalRuleCond[rule,con])	)
    and some { r:applicableRules[req] |evalRuleCond[r,con]}
}

//**************************
//***Hidden data property***
//**************************

fun documents[res:Resource]: set Resource{
    { rt : Resource | rt in res.^resSucc and no rt.resSucc}
}

fun documentsG[]: set Resource{    { rt : Resource | no rt.resSucc}}

fun persons[s:Subject]: set Subject{
    { sub: Subject | sub in s.^subSucc and no sub.subSucc}
}

fun personsG[]: set Subject{
    { sub: Subject | no sub.subSucc}
}

pred HiddenDocument[reso:Resource,c:Context]{
    no req: Request | (req.res = reso and
    access_condition[req,c])
}

    pred HiddenData[c:Context] {
    some reso: documentsG[] | HiddenDocument[reso,c]
}
//***Hidden Data Existence and determination***
check HiddenDocument_r0_c0{ HiddenDocument[r0,c0]} for 4
check HiddenDocument_r0_c1{ HiddenDocument[r0,c1]} for 4
check HiddenDocument_r0_c2{ HiddenDocument[r0,c2]} for 4
check HiddenDocument_r0_c3{ HiddenDocument[r0,c3]} for 4
check HiddenDocument_r0_c4{ HiddenDocument[r0,c4]} for 4
check HiddenDocument_r0_c5{ HiddenDocument[r0,c5]} for 4
check HiddenDocument_r0_c6{ HiddenDocument[r0,c6]} for 4
check HiddenDocument_r0_c7{ HiddenDocument[r0,c7]} for 4
check HiddenDocument_r0_c8{ HiddenDocument[r0,c8]} for 4
check HiddenDocument_r0_c9{ HiddenDocument[r0,c9]} for 4
