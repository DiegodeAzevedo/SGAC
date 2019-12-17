module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s5+
         s8->s0+
         s8->s3+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s6+
         s10->s7}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r6+
         r8->r7+
         r9->r2+
         r9->r4+
         r9->r6+
         r9->r7}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s7
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r5
    m = prohibition
    p = 0
    c = c5
}
one sig rule1 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 2
    c = c8+c6+c7+c0+c5
}
one sig rule2 extends Rule{}{
    s =s4
    t =r3
    m = permission
    p = 2
    c = c1+c3+c0
}
one sig rule3 extends Rule{}{
    s =s2
    t =r5
    m = permission
    p = 0
    c = c1+c7+c5+c0+c2
}
one sig rule4 extends Rule{}{
    s =s1
    t =r6
    m = prohibition
    p = 0
    c = c1+c2+c8+c3+c0+c4
}
one sig rule5 extends Rule{}{
    s =s0
    t =r9
    m = prohibition
    p = 4
    c = c3+c7+c8+c1
}
one sig rule6 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 3
    c = c9+c8+c5+c4+c3
}
one sig rule7 extends Rule{}{
    s =s3
    t =r3
    m = prohibition
    p = 4
    c = c6
}
one sig rule8 extends Rule{}{
    s =s4
    t =r0
    m = prohibition
    p = 0
    c = c3+c2+c7+c1+c9
}
one sig rule9 extends Rule{}{
    s =s0
    t =r7
    m = permission
    p = 2
    c = c1+c9+c3+c8+c0+c5+c2
}
one sig rule10 extends Rule{}{
    s =s0
    t =r2
    m = prohibition
    p = 0
    c = c1+c7+c6+c3+c0+c8
}
one sig rule11 extends Rule{}{
    s =s10
    t =r0
    m = permission
    p = 4
    c = c1+c3+c6+c7+c4
}
one sig rule12 extends Rule{}{
    s =s9
    t =r8
    m = permission
    p = 3
    c = c0+c3+c8
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
