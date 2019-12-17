module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s1+
         s4->s2+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s3+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s8+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s9+
         s13->s11+
         s14->s4+
         s14->s5+
         s14->s9+
         s14->s11+
         s15->s5+
         s15->s9+
         s15->s11+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s9+
         s18->s10+
         s18->s15+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s10+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r0+
         r4->r3+
         r5->r1+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r5+
         r8->r0+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r9+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r2+
         r12->r4+
         r12->r6+
         r12->r9+
         r13->r0+
         r13->r3+
         r13->r5+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r4+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r14+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r12+
         r18->r13+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r16+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req7 extends Request{}{
sub=s1
res=r7
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s11
    t =r18
    m = permission
    p = 3
    c = c8+c2+c9+c3+c6+c1
}
one sig rule1 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 0
    c = c2+c7+c9+c3+c0+c5
}
one sig rule2 extends Rule{}{
    s =s14
    t =r17
    m = permission
    p = 4
    c = c3
}
one sig rule3 extends Rule{}{
    s =s4
    t =r12
    m = prohibition
    p = 1
    c = c7+c5
}
one sig rule4 extends Rule{}{
    s =s11
    t =r14
    m = prohibition
    p = 1
    c = c1+c8+c0
}
one sig rule5 extends Rule{}{
    s =s0
    t =r14
    m = prohibition
    p = 3
    c = c8
}
one sig rule6 extends Rule{}{
    s =s15
    t =r10
    m = permission
    p = 1
    c = c0+c1+c4+c5
}
one sig rule7 extends Rule{}{
    s =s9
    t =r5
    m = permission
    p = 1
    c = c3
}
one sig rule8 extends Rule{}{
    s =s1
    t =r13
    m = prohibition
    p = 2
    c = c7+c2+c9+c3+c5+c1+c0
}
one sig rule9 extends Rule{}{
    s =s3
    t =r7
    m = permission
    p = 0
    c = c7+c2
}
one sig rule10 extends Rule{}{
    s =s4
    t =r13
    m = prohibition
    p = 1
    c = c2+c9+c1+c5+c6+c3
}
one sig rule11 extends Rule{}{
    s =s5
    t =r13
    m = prohibition
    p = 4
    c = c5+c9+c4+c7+c2+c0
}
one sig rule12 extends Rule{}{
    s =s18
    t =r6
    m = permission
    p = 2
    c = c0+c2
}
one sig rule13 extends Rule{}{
    s =s1
    t =r1
    m = permission
    p = 4
    c = c9+c3+c7+c0+c6+c8
}
one sig rule14 extends Rule{}{
    s =s5
    t =r14
    m = prohibition
    p = 2
    c = c2+c7+c1+c3+c4
}
one sig rule15 extends Rule{}{
    s =s7
    t =r0
    m = prohibition
    p = 4
    c = c0+c2+c4+c8+c7+c1
}
one sig rule16 extends Rule{}{
    s =s13
    t =r7
    m = permission
    p = 2
    c = c4+c0
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
check HiddenDocument_r7_c0{ HiddenDocument[r7,c0]} for 4
check HiddenDocument_r7_c1{ HiddenDocument[r7,c1]} for 4
check HiddenDocument_r7_c2{ HiddenDocument[r7,c2]} for 4
check HiddenDocument_r7_c3{ HiddenDocument[r7,c3]} for 4
check HiddenDocument_r7_c4{ HiddenDocument[r7,c4]} for 4
check HiddenDocument_r7_c5{ HiddenDocument[r7,c5]} for 4
check HiddenDocument_r7_c6{ HiddenDocument[r7,c6]} for 4
check HiddenDocument_r7_c7{ HiddenDocument[r7,c7]} for 4
check HiddenDocument_r7_c8{ HiddenDocument[r7,c8]} for 4
check HiddenDocument_r7_c9{ HiddenDocument[r7,c9]} for 4
