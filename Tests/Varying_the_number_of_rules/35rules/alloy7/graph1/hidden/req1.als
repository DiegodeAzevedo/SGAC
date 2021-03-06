module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s1+
         s4->s2+
         s4->s3+
         s5->s2+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s6+
         s9->s0+
         s9->s1+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s4+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s6+
         s18->s8+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s13+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r2+
         r8->r5+
         r9->r2+
         r9->r3+
         r9->r6+
         r10->r0+
         r10->r3+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r9+
         r12->r0+
         r12->r4+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r3+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
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
    s =s9
    t =r9
    m = prohibition
    p = 4
    c = c9
}
one sig rule1 extends Rule{}{
    s =s13
    t =r3
    m = permission
    p = 1
    c = c3+c1+c8+c9
}
one sig rule2 extends Rule{}{
    s =s1
    t =r12
    m = permission
    p = 3
    c = c5+c7+c4+c1+c2
}
one sig rule3 extends Rule{}{
    s =s11
    t =r17
    m = permission
    p = 0
    c = c2+c0+c4+c5+c9+c7+c3
}
one sig rule4 extends Rule{}{
    s =s19
    t =r6
    m = permission
    p = 2
    c = c9+c0+c8+c2
}
one sig rule5 extends Rule{}{
    s =s7
    t =r2
    m = prohibition
    p = 3
    c = c7
}
one sig rule6 extends Rule{}{
    s =s3
    t =r12
    m = prohibition
    p = 3
    c = c0+c7+c4
}
one sig rule7 extends Rule{}{
    s =s0
    t =r0
    m = prohibition
    p = 4
    c = c9+c3+c2
}
one sig rule8 extends Rule{}{
    s =s13
    t =r19
    m = permission
    p = 4
    c = c2+c9+c8+c7+c6+c5
}
one sig rule9 extends Rule{}{
    s =s11
    t =r13
    m = permission
    p = 0
    c = c6+c1+c3+c8+c2+c4
}
one sig rule10 extends Rule{}{
    s =s6
    t =r19
    m = prohibition
    p = 4
    c = c8+c6
}
one sig rule11 extends Rule{}{
    s =s18
    t =r14
    m = permission
    p = 2
    c = c5+c4
}
one sig rule12 extends Rule{}{
    s =s16
    t =r16
    m = prohibition
    p = 4
    c = c9+c0+c4
}
one sig rule13 extends Rule{}{
    s =s4
    t =r5
    m = permission
    p = 4
    c = c6+c4+c5
}
one sig rule14 extends Rule{}{
    s =s0
    t =r0
    m = permission
    p = 3
    c = c8+c4
}
one sig rule15 extends Rule{}{
    s =s8
    t =r13
    m = prohibition
    p = 3
    c = c7+c3+c5+c6+c2+c1
}
one sig rule16 extends Rule{}{
    s =s12
    t =r6
    m = prohibition
    p = 1
    c = c4+c9+c0+c2
}
one sig rule17 extends Rule{}{
    s =s3
    t =r13
    m = permission
    p = 4
    c = c0+c3+c6+c1
}
one sig rule18 extends Rule{}{
    s =s3
    t =r8
    m = prohibition
    p = 3
    c = c6+c1+c3+c5
}
one sig rule19 extends Rule{}{
    s =s10
    t =r0
    m = prohibition
    p = 0
    c = c9
}
one sig rule20 extends Rule{}{
    s =s11
    t =r12
    m = permission
    p = 1
    c = c6+c2+c3+c9
}
one sig rule21 extends Rule{}{
    s =s4
    t =r19
    m = prohibition
    p = 0
    c = c2+c4+c8
}
one sig rule22 extends Rule{}{
    s =s16
    t =r17
    m = prohibition
    p = 4
    c = c2+c1+c4
}
one sig rule23 extends Rule{}{
    s =s5
    t =r9
    m = prohibition
    p = 2
    c = c1
}
one sig rule24 extends Rule{}{
    s =s3
    t =r17
    m = prohibition
    p = 0
    c = c0+c1
}
one sig rule25 extends Rule{}{
    s =s8
    t =r11
    m = permission
    p = 3
    c = c7+c8+c2
}
one sig rule26 extends Rule{}{
    s =s10
    t =r15
    m = permission
    p = 2
    c = c3+c2+c9+c0
}
one sig rule27 extends Rule{}{
    s =s16
    t =r4
    m = permission
    p = 0
    c = c7+c9+c2+c6+c4+c0+c3
}
one sig rule28 extends Rule{}{
    s =s11
    t =r13
    m = prohibition
    p = 3
    c = c4+c2+c1
}
one sig rule29 extends Rule{}{
    s =s17
    t =r4
    m = prohibition
    p = 1
    c = c6+c9+c7+c8
}
one sig rule30 extends Rule{}{
    s =s19
    t =r3
    m = prohibition
    p = 4
    c = c6+c9+c7+c1+c5
}
one sig rule31 extends Rule{}{
    s =s8
    t =r4
    m = prohibition
    p = 3
    c = c9+c2+c4+c8
}
one sig rule32 extends Rule{}{
    s =s19
    t =r12
    m = permission
    p = 4
    c = c6+c8+c2
}
one sig rule33 extends Rule{}{
    s =s11
    t =r16
    m = permission
    p = 2
    c = c5+c9+c6+c3
}
one sig rule34 extends Rule{}{
    s =s13
    t =r6
    m = permission
    p = 3
    c = c2
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
