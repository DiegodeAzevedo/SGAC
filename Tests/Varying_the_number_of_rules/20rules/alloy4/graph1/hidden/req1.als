module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s2+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s8->s4+
         s8->s7+
         s9->s2+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s5+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s5+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s15->s2+
         s15->s5+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s15+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s3+
         s19->s4+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r8->r0+
         r8->r2+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r7+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r6+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r12+
         r15->r0+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r13+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r6+
         r17->r10+
         r17->r11+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r8+
         r18->r10+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r5+
         r19->r7+
         r19->r14+
         r19->r15+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r10
    m = prohibition
    p = 0
    c = c4+c8+c6
}
one sig rule1 extends Rule{}{
    s =s12
    t =r18
    m = prohibition
    p = 0
    c = c2+c3+c4
}
one sig rule2 extends Rule{}{
    s =s9
    t =r8
    m = permission
    p = 4
    c = c2+c4+c3+c5
}
one sig rule3 extends Rule{}{
    s =s3
    t =r17
    m = permission
    p = 0
    c = c5+c0
}
one sig rule4 extends Rule{}{
    s =s10
    t =r12
    m = prohibition
    p = 1
    c = c3+c8+c0+c7+c2
}
one sig rule5 extends Rule{}{
    s =s11
    t =r0
    m = permission
    p = 1
    c = c3+c6+c4+c2+c1
}
one sig rule6 extends Rule{}{
    s =s12
    t =r3
    m = permission
    p = 2
    c = c9+c0
}
one sig rule7 extends Rule{}{
    s =s8
    t =r3
    m = prohibition
    p = 4
    c = c0+c1
}
one sig rule8 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 3
    c = c8
}
one sig rule9 extends Rule{}{
    s =s17
    t =r9
    m = prohibition
    p = 1
    c = c8+c6
}
one sig rule10 extends Rule{}{
    s =s2
    t =r12
    m = permission
    p = 0
    c = c2+c6+c7+c9+c0+c3
}
one sig rule11 extends Rule{}{
    s =s5
    t =r9
    m = permission
    p = 2
    c = c5+c2+c3+c6
}
one sig rule12 extends Rule{}{
    s =s2
    t =r6
    m = permission
    p = 2
    c = c2+c3+c8
}
one sig rule13 extends Rule{}{
    s =s7
    t =r16
    m = permission
    p = 3
    c = c4+c6+c1+c9+c7+c5+c2+c8
}
one sig rule14 extends Rule{}{
    s =s3
    t =r6
    m = permission
    p = 0
    c = c7+c9+c4+c5+c0
}
one sig rule15 extends Rule{}{
    s =s1
    t =r2
    m = prohibition
    p = 2
    c = c9+c8+c4+c3+c6
}
one sig rule16 extends Rule{}{
    s =s11
    t =r18
    m = prohibition
    p = 4
    c = c1+c7+c5+c6+c9+c0
}
one sig rule17 extends Rule{}{
    s =s17
    t =r12
    m = prohibition
    p = 0
    c = c3
}
one sig rule18 extends Rule{}{
    s =s6
    t =r8
    m = permission
    p = 3
    c = c0+c2
}
one sig rule19 extends Rule{}{
    s =s16
    t =r5
    m = permission
    p = 1
    c = c5+c9+c6+c2+c1+c7
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
check HiddenDocument_r4_c0{ HiddenDocument[r4,c0]} for 4
check HiddenDocument_r4_c1{ HiddenDocument[r4,c1]} for 4
check HiddenDocument_r4_c2{ HiddenDocument[r4,c2]} for 4
check HiddenDocument_r4_c3{ HiddenDocument[r4,c3]} for 4
check HiddenDocument_r4_c4{ HiddenDocument[r4,c4]} for 4
check HiddenDocument_r4_c5{ HiddenDocument[r4,c5]} for 4
check HiddenDocument_r4_c6{ HiddenDocument[r4,c6]} for 4
check HiddenDocument_r4_c7{ HiddenDocument[r4,c7]} for 4
check HiddenDocument_r4_c8{ HiddenDocument[r4,c8]} for 4
check HiddenDocument_r4_c9{ HiddenDocument[r4,c9]} for 4
