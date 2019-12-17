module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s6->s1+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s9+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s11+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s12+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r3->r2+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r6+
         r10->r8+
         r11->r2+
         r11->r4+
         r11->r10+
         r12->r2+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r13+
         r15->r1+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r13+
         r19->r14}

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
    s =s18
    t =r7
    m = permission
    p = 2
    c = c7+c1+c5+c8+c3+c9
}
one sig rule1 extends Rule{}{
    s =s10
    t =r9
    m = prohibition
    p = 0
    c = c1+c2+c8+c4+c7
}
one sig rule2 extends Rule{}{
    s =s11
    t =r4
    m = permission
    p = 0
    c = c8+c3+c2+c0+c7
}
one sig rule3 extends Rule{}{
    s =s2
    t =r10
    m = permission
    p = 2
    c = c0+c7+c4+c6
}
one sig rule4 extends Rule{}{
    s =s17
    t =r0
    m = permission
    p = 3
    c = c1+c8+c3+c6
}
one sig rule5 extends Rule{}{
    s =s0
    t =r9
    m = prohibition
    p = 0
    c = c1+c0
}
one sig rule6 extends Rule{}{
    s =s10
    t =r18
    m = permission
    p = 0
    c = c2
}
one sig rule7 extends Rule{}{
    s =s4
    t =r8
    m = permission
    p = 4
    c = c2+c5+c6
}
one sig rule8 extends Rule{}{
    s =s13
    t =r15
    m = prohibition
    p = 0
    c = c5+c0+c9+c3
}
one sig rule9 extends Rule{}{
    s =s2
    t =r12
    m = prohibition
    p = 1
    c = c7+c4+c6+c9+c8+c5+c1+c3
}
one sig rule10 extends Rule{}{
    s =s19
    t =r12
    m = prohibition
    p = 3
    c = c2+c8+c3+c6+c5
}
one sig rule11 extends Rule{}{
    s =s0
    t =r10
    m = permission
    p = 4
    c = c3+c1+c9+c8+c0+c5
}
one sig rule12 extends Rule{}{
    s =s4
    t =r2
    m = prohibition
    p = 2
    c = c5+c0
}
one sig rule13 extends Rule{}{
    s =s5
    t =r15
    m = prohibition
    p = 3
    c = c0+c5+c3+c4+c2
}
one sig rule14 extends Rule{}{
    s =s18
    t =r8
    m = permission
    p = 4
    c = c2+c5+c6
}
one sig rule15 extends Rule{}{
    s =s1
    t =r11
    m = permission
    p = 1
    c = c3+c2+c7+c4
}
one sig rule16 extends Rule{}{
    s =s3
    t =r16
    m = prohibition
    p = 2
    c = c5+c7+c2+c4+c8+c0
}
one sig rule17 extends Rule{}{
    s =s8
    t =r3
    m = permission
    p = 1
    c = c0+c8
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
