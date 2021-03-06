module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s1+
         s4->s0+
         s4->s2+
         s5->s1+
         s5->s2+
         s6->s1+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s12}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r6+
         r10->r8+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11}

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
    s =s6
    t =r10
    m = permission
    p = 1
    c = c5+c9+c3+c0+c7
}
one sig rule1 extends Rule{}{
    s =s6
    t =r4
    m = prohibition
    p = 4
    c = c4+c5+c8+c6+c1+c2
}
one sig rule2 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 3
    c = c2+c5+c1
}
one sig rule3 extends Rule{}{
    s =s8
    t =r2
    m = permission
    p = 2
    c = c8+c9+c7+c6
}
one sig rule4 extends Rule{}{
    s =s2
    t =r10
    m = prohibition
    p = 3
    c = c4+c1+c9
}
one sig rule5 extends Rule{}{
    s =s1
    t =r5
    m = prohibition
    p = 2
    c = c5+c1+c7+c8+c3+c9
}
one sig rule6 extends Rule{}{
    s =s0
    t =r10
    m = permission
    p = 2
    c = c1+c7+c3+c5+c6+c0+c4+c8
}
one sig rule7 extends Rule{}{
    s =s2
    t =r9
    m = prohibition
    p = 0
    c = c2+c9+c7
}
one sig rule8 extends Rule{}{
    s =s7
    t =r4
    m = prohibition
    p = 0
    c = c2+c0+c8+c1+c9
}
one sig rule9 extends Rule{}{
    s =s13
    t =r6
    m = prohibition
    p = 1
    c = c6
}
one sig rule10 extends Rule{}{
    s =s11
    t =r12
    m = permission
    p = 1
    c = c1+c2+c5+c3+c0+c9
}
one sig rule11 extends Rule{}{
    s =s12
    t =r2
    m = permission
    p = 3
    c = c5+c0+c4
}
one sig rule12 extends Rule{}{
    s =s12
    t =r9
    m = prohibition
    p = 4
    c = c9+c1+c4+c8+c3+c2
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
check HiddenDocument_r1_c0{ HiddenDocument[r1,c0]} for 4
check HiddenDocument_r1_c1{ HiddenDocument[r1,c1]} for 4
check HiddenDocument_r1_c2{ HiddenDocument[r1,c2]} for 4
check HiddenDocument_r1_c3{ HiddenDocument[r1,c3]} for 4
check HiddenDocument_r1_c4{ HiddenDocument[r1,c4]} for 4
check HiddenDocument_r1_c5{ HiddenDocument[r1,c5]} for 4
check HiddenDocument_r1_c6{ HiddenDocument[r1,c6]} for 4
check HiddenDocument_r1_c7{ HiddenDocument[r1,c7]} for 4
check HiddenDocument_r1_c8{ HiddenDocument[r1,c8]} for 4
check HiddenDocument_r1_c9{ HiddenDocument[r1,c9]} for 4
