module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s10->s4+
         s10->s7+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s7+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s8+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s7+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s17->s0+
         s17->s2+
         s17->s6+
         s17->s9+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16 extends Resource{}{}
fact{
resSucc=r2->r1+
         r4->r3+
         r5->r0+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r5+
         r8->r2+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r6+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r6+
         r13->r9+
         r13->r12+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r11+
         r15->r1+
         r15->r3+
         r15->r8+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r13}

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
    s =s4
    t =r13
    m = permission
    p = 4
    c = c3+c4
}
one sig rule1 extends Rule{}{
    s =s3
    t =r8
    m = permission
    p = 4
    c = c9+c4+c6+c1+c3+c7+c5
}
one sig rule2 extends Rule{}{
    s =s8
    t =r12
    m = permission
    p = 4
    c = c2
}
one sig rule3 extends Rule{}{
    s =s8
    t =r5
    m = permission
    p = 2
    c = c6+c3+c5+c0
}
one sig rule4 extends Rule{}{
    s =s15
    t =r4
    m = permission
    p = 1
    c = c5+c0+c8
}
one sig rule5 extends Rule{}{
    s =s7
    t =r13
    m = prohibition
    p = 1
    c = c3+c9+c7+c4+c1+c0
}
one sig rule6 extends Rule{}{
    s =s10
    t =r12
    m = permission
    p = 3
    c = c4+c5+c1+c8+c7
}
one sig rule7 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 0
    c = c1
}
one sig rule8 extends Rule{}{
    s =s11
    t =r9
    m = prohibition
    p = 1
    c = c3+c8+c4+c1+c7
}
one sig rule9 extends Rule{}{
    s =s12
    t =r15
    m = permission
    p = 1
    c = c3+c1+c5+c0
}
one sig rule10 extends Rule{}{
    s =s6
    t =r5
    m = permission
    p = 3
    c = c7+c6+c3
}
one sig rule11 extends Rule{}{
    s =s14
    t =r8
    m = prohibition
    p = 3
    c = c8+c2+c6+c7+c9+c3
}
one sig rule12 extends Rule{}{
    s =s11
    t =r0
    m = permission
    p = 4
    c = c4+c8+c7
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
