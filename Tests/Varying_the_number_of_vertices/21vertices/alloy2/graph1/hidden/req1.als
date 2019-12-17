module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s1+
         s5->s0+
         s5->s2+
         s6->s0+
         s6->s3+
         s7->s1+
         s7->s2+
         s7->s4+
         s8->s1+
         s8->s2+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s7+
         s10->s8+
         s10->s9}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r2+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6}

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
    s =s7
    t =r4
    m = permission
    p = 3
    c = c0+c4+c6+c9+c3+c2+c5
}
one sig rule1 extends Rule{}{
    s =s5
    t =r5
    m = prohibition
    p = 3
    c = c7+c4+c2+c8
}
one sig rule2 extends Rule{}{
    s =s1
    t =r9
    m = prohibition
    p = 4
    c = c7+c9+c0+c6+c3
}
one sig rule3 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 2
    c = c5+c4+c1+c2
}
one sig rule4 extends Rule{}{
    s =s6
    t =r1
    m = permission
    p = 3
    c = c5+c0+c9
}
one sig rule5 extends Rule{}{
    s =s9
    t =r6
    m = prohibition
    p = 0
    c = c6+c9+c5+c3
}
one sig rule6 extends Rule{}{
    s =s9
    t =r2
    m = prohibition
    p = 2
    c = c3+c2+c1+c9+c5
}
one sig rule7 extends Rule{}{
    s =s2
    t =r9
    m = permission
    p = 0
    c = c2+c7+c6+c9
}
one sig rule8 extends Rule{}{
    s =s0
    t =r2
    m = prohibition
    p = 0
    c = c6+c1
}
one sig rule9 extends Rule{}{
    s =s9
    t =r9
    m = prohibition
    p = 1
    c = c2+c7+c3+c1+c4
}
one sig rule10 extends Rule{}{
    s =s8
    t =r3
    m = prohibition
    p = 4
    c = c0+c5+c6+c2
}
one sig rule11 extends Rule{}{
    s =s1
    t =r2
    m = permission
    p = 4
    c = c2+c0+c8+c7
}
one sig rule12 extends Rule{}{
    s =s7
    t =r3
    m = prohibition
    p = 1
    c = c4+c2+c1+c9+c3
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
