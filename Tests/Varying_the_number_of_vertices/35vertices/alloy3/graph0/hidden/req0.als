module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s6+
         s10->s0+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s8+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s9+
         s13->s11+
         s14->s3+
         s14->s5+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s2+
         s16->s5+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s12}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16 extends Resource{}{}
fact{
resSucc=r3->r1+
         r4->r0+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r8->r4+
         r8->r5+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r7+
         r11->r10+
         r12->r0+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r9+
         r13->r12+
         r14->r4+
         r14->r5+
         r14->r8+
         r14->r9+
         r14->r11+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r7+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r13+
         r16->r14+
         r16->r15}

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
    s =s14
    t =r9
    m = prohibition
    p = 1
    c = c8+c2+c0+c5+c7
}
one sig rule1 extends Rule{}{
    s =s8
    t =r10
    m = prohibition
    p = 0
    c = c2+c6
}
one sig rule2 extends Rule{}{
    s =s2
    t =r15
    m = prohibition
    p = 4
    c = c4+c2+c8
}
one sig rule3 extends Rule{}{
    s =s11
    t =r0
    m = permission
    p = 0
    c = c0+c4+c1+c7
}
one sig rule4 extends Rule{}{
    s =s2
    t =r10
    m = prohibition
    p = 4
    c = c4+c1+c0+c3
}
one sig rule5 extends Rule{}{
    s =s16
    t =r10
    m = prohibition
    p = 4
    c = c0+c4+c9+c6
}
one sig rule6 extends Rule{}{
    s =s11
    t =r1
    m = prohibition
    p = 3
    c = c1+c4+c3+c9+c8
}
one sig rule7 extends Rule{}{
    s =s0
    t =r11
    m = permission
    p = 0
    c = c1
}
one sig rule8 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 2
    c = c8+c0+c3+c1+c9
}
one sig rule9 extends Rule{}{
    s =s13
    t =r14
    m = prohibition
    p = 1
    c = c5+c4+c1+c0+c8+c3
}
one sig rule10 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 1
    c = c7+c9
}
one sig rule11 extends Rule{}{
    s =s8
    t =r2
    m = permission
    p = 1
    c = c5+c8+c4+c9+c0+c7
}
one sig rule12 extends Rule{}{
    s =s8
    t =r8
    m = prohibition
    p = 3
    c = c6+c2
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
