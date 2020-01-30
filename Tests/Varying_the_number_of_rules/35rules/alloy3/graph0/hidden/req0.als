module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s4->s1+
         s4->s3+
         s5->s0+
         s6->s0+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s0+
         s8->s2+
         s8->s3+
         s9->s2+
         s9->s3+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s5+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s3+
         s19->s5+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r3+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r4+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r10+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r14+
         r18->r2+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r12+
         r19->r16+
         r19->r18}

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
    s =s6
    t =r17
    m = permission
    p = 2
    c = c3+c9+c4+c5+c7+c6+c2+c8+c1
}
one sig rule1 extends Rule{}{
    s =s17
    t =r14
    m = permission
    p = 4
    c = c2+c8+c0+c6+c9
}
one sig rule2 extends Rule{}{
    s =s12
    t =r12
    m = prohibition
    p = 0
    c = c7+c0+c8+c3+c5+c4+c2
}
one sig rule3 extends Rule{}{
    s =s17
    t =r17
    m = permission
    p = 3
    c = c1
}
one sig rule4 extends Rule{}{
    s =s16
    t =r2
    m = permission
    p = 2
    c = c2
}
one sig rule5 extends Rule{}{
    s =s3
    t =r5
    m = permission
    p = 0
    c = c7+c1+c8+c0
}
one sig rule6 extends Rule{}{
    s =s11
    t =r5
    m = permission
    p = 1
    c = c2+c9+c5
}
one sig rule7 extends Rule{}{
    s =s16
    t =r6
    m = prohibition
    p = 1
    c = c4+c6+c1+c2
}
one sig rule8 extends Rule{}{
    s =s5
    t =r16
    m = permission
    p = 3
    c = c5+c0
}
one sig rule9 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 2
    c = c4+c3
}
one sig rule10 extends Rule{}{
    s =s6
    t =r3
    m = permission
    p = 4
    c = c8+c5
}
one sig rule11 extends Rule{}{
    s =s3
    t =r14
    m = permission
    p = 2
    c = c6+c3+c8+c1+c7
}
one sig rule12 extends Rule{}{
    s =s19
    t =r16
    m = prohibition
    p = 4
    c = c0+c8+c5
}
one sig rule13 extends Rule{}{
    s =s6
    t =r1
    m = permission
    p = 4
    c = c6+c8
}
one sig rule14 extends Rule{}{
    s =s19
    t =r18
    m = prohibition
    p = 3
    c = c8+c0
}
one sig rule15 extends Rule{}{
    s =s17
    t =r6
    m = permission
    p = 2
    c = c0+c2
}
one sig rule16 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 3
    c = c4+c8+c7
}
one sig rule17 extends Rule{}{
    s =s9
    t =r4
    m = prohibition
    p = 2
    c = c4+c1
}
one sig rule18 extends Rule{}{
    s =s17
    t =r7
    m = prohibition
    p = 0
    c = c6+c2+c0+c1+c7+c9
}
one sig rule19 extends Rule{}{
    s =s5
    t =r10
    m = permission
    p = 3
    c = c8
}
one sig rule20 extends Rule{}{
    s =s13
    t =r17
    m = permission
    p = 1
    c = c2+c6
}
one sig rule21 extends Rule{}{
    s =s15
    t =r17
    m = prohibition
    p = 0
    c = c3+c4+c1+c5+c6
}
one sig rule22 extends Rule{}{
    s =s14
    t =r16
    m = permission
    p = 4
    c = c5+c2+c0+c8+c7
}
one sig rule23 extends Rule{}{
    s =s19
    t =r8
    m = prohibition
    p = 2
    c = c5+c4+c7+c6+c3+c9+c2
}
one sig rule24 extends Rule{}{
    s =s0
    t =r11
    m = prohibition
    p = 2
    c = c3+c2+c0
}
one sig rule25 extends Rule{}{
    s =s5
    t =r6
    m = permission
    p = 1
    c = c3+c5+c1+c2+c7+c9+c6
}
one sig rule26 extends Rule{}{
    s =s16
    t =r13
    m = prohibition
    p = 3
    c = c9+c1+c7+c5+c3
}
one sig rule27 extends Rule{}{
    s =s2
    t =r16
    m = permission
    p = 1
    c = c7+c5+c6+c2+c8+c9
}
one sig rule28 extends Rule{}{
    s =s9
    t =r11
    m = prohibition
    p = 4
    c = c6+c7+c8+c4+c5+c2+c9+c0
}
one sig rule29 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 1
    c = c2+c9+c3
}
one sig rule30 extends Rule{}{
    s =s1
    t =r3
    m = permission
    p = 2
    c = c3+c5
}
one sig rule31 extends Rule{}{
    s =s11
    t =r13
    m = permission
    p = 4
    c = c6+c8+c1+c2
}
one sig rule32 extends Rule{}{
    s =s12
    t =r6
    m = permission
    p = 3
    c = c3+c8+c1+c6+c2+c4
}
one sig rule33 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 0
    c = c2+c6+c7+c8+c4+c5
}
one sig rule34 extends Rule{}{
    s =s3
    t =r12
    m = prohibition
    p = 3
    c = c9+c4
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
