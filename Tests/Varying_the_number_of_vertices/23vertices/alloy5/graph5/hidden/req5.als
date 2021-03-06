module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s4+
         s7->s1+
         s7->s2+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s9->s4+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s6+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r7->r0+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r5+
         r8->r7+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r9}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s0
    t =r6
    m = permission
    p = 1
    c = c7+c3+c0+c4+c6+c8
}
one sig rule1 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 0
    c = c9+c3+c4
}
one sig rule2 extends Rule{}{
    s =s3
    t =r9
    m = prohibition
    p = 2
    c = c0+c9+c2+c4+c7
}
one sig rule3 extends Rule{}{
    s =s8
    t =r10
    m = prohibition
    p = 4
    c = c9+c1+c3+c5+c6+c2
}
one sig rule4 extends Rule{}{
    s =s0
    t =r10
    m = prohibition
    p = 4
    c = c8
}
one sig rule5 extends Rule{}{
    s =s8
    t =r9
    m = prohibition
    p = 0
    c = c8+c6+c7+c3+c5+c2
}
one sig rule6 extends Rule{}{
    s =s5
    t =r4
    m = permission
    p = 0
    c = c2+c5+c7+c9+c8+c3
}
one sig rule7 extends Rule{}{
    s =s8
    t =r3
    m = permission
    p = 4
    c = c0+c7
}
one sig rule8 extends Rule{}{
    s =s7
    t =r1
    m = prohibition
    p = 3
    c = c4+c2+c3+c9+c0+c6+c8+c7+c1
}
one sig rule9 extends Rule{}{
    s =s7
    t =r8
    m = prohibition
    p = 4
    c = c0+c2+c4+c1+c9
}
one sig rule10 extends Rule{}{
    s =s2
    t =r0
    m = permission
    p = 1
    c = c7+c6
}
one sig rule11 extends Rule{}{
    s =s2
    t =r7
    m = permission
    p = 2
    c = c5+c7+c3+c4+c9+c8+c6
}
one sig rule12 extends Rule{}{
    s =s8
    t =r7
    m = permission
    p = 2
    c = c9+c4+c6
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
