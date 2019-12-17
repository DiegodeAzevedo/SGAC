module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s6+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s4+
         s11->s5+
         s11->s8+
         s12->s1+
         s12->s3+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s5+
         s13->s6+
         s13->s10+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s10+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s12+
         s18->s15+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r2+
         r5->r0+
         r5->r3+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r4+
         r7->r5+
         r8->r3+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r8+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r8+
         r13->r0+
         r13->r6+
         r13->r12+
         r14->r1+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r12+
         r16->r2+
         r16->r3+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r8+
         r17->r11+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r17+
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
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r8
    m = prohibition
    p = 2
    c = c2+c3+c6+c9+c8+c1+c4
}
one sig rule1 extends Rule{}{
    s =s14
    t =r13
    m = prohibition
    p = 4
    c = c9+c1+c6+c2+c8+c0
}
one sig rule2 extends Rule{}{
    s =s19
    t =r18
    m = prohibition
    p = 3
    c = c8+c0
}
one sig rule3 extends Rule{}{
    s =s13
    t =r12
    m = prohibition
    p = 3
    c = c7+c2+c4
}
one sig rule4 extends Rule{}{
    s =s15
    t =r2
    m = permission
    p = 1
    c = c7+c4+c9
}
one sig rule5 extends Rule{}{
    s =s1
    t =r5
    m = prohibition
    p = 3
    c = c5+c9+c2+c3+c7
}
one sig rule6 extends Rule{}{
    s =s3
    t =r4
    m = prohibition
    p = 1
    c = c9+c0+c4+c1+c2+c5+c7
}
one sig rule7 extends Rule{}{
    s =s18
    t =r12
    m = prohibition
    p = 1
    c = c8+c9+c1+c2+c7+c4+c0
}
one sig rule8 extends Rule{}{
    s =s6
    t =r9
    m = prohibition
    p = 4
    c = c9+c2+c7+c4+c5
}
one sig rule9 extends Rule{}{
    s =s12
    t =r4
    m = permission
    p = 3
    c = c6+c1
}
one sig rule10 extends Rule{}{
    s =s4
    t =r18
    m = prohibition
    p = 4
    c = c0+c8+c3
}
one sig rule11 extends Rule{}{
    s =s11
    t =r19
    m = permission
    p = 1
    c = c6
}
one sig rule12 extends Rule{}{
    s =s6
    t =r17
    m = permission
    p = 1
    c = c6+c9
}
one sig rule13 extends Rule{}{
    s =s18
    t =r18
    m = permission
    p = 1
    c = c8+c2
}
one sig rule14 extends Rule{}{
    s =s18
    t =r6
    m = prohibition
    p = 4
    c = c0+c7+c3+c1+c5+c2
}
one sig rule15 extends Rule{}{
    s =s14
    t =r14
    m = prohibition
    p = 1
    c = c1+c6+c7+c9+c3+c5
}
one sig rule16 extends Rule{}{
    s =s6
    t =r0
    m = permission
    p = 4
    c = c5+c8
}
one sig rule17 extends Rule{}{
    s =s5
    t =r6
    m = permission
    p = 0
    c = c8+c7+c1+c5
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
