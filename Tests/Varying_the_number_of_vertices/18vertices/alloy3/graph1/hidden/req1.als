module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s3+
         s8->s6}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r4->r3+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 4
    c = c3+c7+c0+c8
}
one sig rule1 extends Rule{}{
    s =s0
    t =r7
    m = prohibition
    p = 1
    c = c6+c8+c5
}
one sig rule2 extends Rule{}{
    s =s3
    t =r3
    m = permission
    p = 3
    c = c2+c5
}
one sig rule3 extends Rule{}{
    s =s8
    t =r6
    m = permission
    p = 0
    c = c6+c2+c3+c9+c8
}
one sig rule4 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 1
    c = c6+c8
}
one sig rule5 extends Rule{}{
    s =s6
    t =r6
    m = prohibition
    p = 2
    c = c0+c9+c2+c4+c3+c1
}
one sig rule6 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 3
    c = c9+c5
}
one sig rule7 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 2
    c = c1+c2+c7
}
one sig rule8 extends Rule{}{
    s =s3
    t =r2
    m = permission
    p = 0
    c = c3+c8+c1+c9+c2
}
one sig rule9 extends Rule{}{
    s =s1
    t =r4
    m = prohibition
    p = 0
    c = c0+c9
}
one sig rule10 extends Rule{}{
    s =s3
    t =r6
    m = permission
    p = 3
    c = c0+c9+c2+c3+c5
}
one sig rule11 extends Rule{}{
    s =s3
    t =r5
    m = permission
    p = 1
    c = c4+c5+c3
}
one sig rule12 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 1
    c = c8+c9+c1+c7
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
check HiddenDocument_r2_c0{ HiddenDocument[r2,c0]} for 4
check HiddenDocument_r2_c1{ HiddenDocument[r2,c1]} for 4
check HiddenDocument_r2_c2{ HiddenDocument[r2,c2]} for 4
check HiddenDocument_r2_c3{ HiddenDocument[r2,c3]} for 4
check HiddenDocument_r2_c4{ HiddenDocument[r2,c4]} for 4
check HiddenDocument_r2_c5{ HiddenDocument[r2,c5]} for 4
check HiddenDocument_r2_c6{ HiddenDocument[r2,c6]} for 4
check HiddenDocument_r2_c7{ HiddenDocument[r2,c7]} for 4
check HiddenDocument_r2_c8{ HiddenDocument[r2,c8]} for 4
check HiddenDocument_r2_c9{ HiddenDocument[r2,c9]} for 4
