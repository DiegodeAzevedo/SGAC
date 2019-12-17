module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s0+
         s4->s2+
         s5->s0+
         s5->s2+
         s6->s1+
         s6->s2+
         s6->s5+
         s7->s0+
         s7->s2+
         s7->s4+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s4+
         s9->s5+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s4+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s8+
         s14->s9+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s14+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s18->s1+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s12+
         s18->s14+
         s19->s0+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s15+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r2+
         r5->r3+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r3+
         r10->r6+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r8+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r9+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r9+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r7+
         r15->r9+
         r15->r11+
         r15->r13+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r5+
         r17->r8+
         r17->r11+
         r17->r14+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r8+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s9
    t =r15
    m = prohibition
    p = 1
    c = c3+c8+c1+c6+c9+c0
}
one sig rule1 extends Rule{}{
    s =s19
    t =r14
    m = prohibition
    p = 0
    c = c1
}
one sig rule2 extends Rule{}{
    s =s17
    t =r6
    m = prohibition
    p = 3
    c = c5+c4+c7+c3+c1
}
one sig rule3 extends Rule{}{
    s =s15
    t =r12
    m = permission
    p = 0
    c = c1+c5+c7+c3+c9+c2
}
one sig rule4 extends Rule{}{
    s =s16
    t =r9
    m = prohibition
    p = 4
    c = c9+c8+c0+c1+c5
}
one sig rule5 extends Rule{}{
    s =s15
    t =r9
    m = permission
    p = 3
    c = c3
}
one sig rule6 extends Rule{}{
    s =s3
    t =r16
    m = prohibition
    p = 3
    c = c7+c2+c8+c9
}
one sig rule7 extends Rule{}{
    s =s14
    t =r5
    m = permission
    p = 4
    c = c3
}
one sig rule8 extends Rule{}{
    s =s17
    t =r0
    m = permission
    p = 4
    c = c1+c3+c8+c6+c5
}
one sig rule9 extends Rule{}{
    s =s3
    t =r11
    m = permission
    p = 2
    c = c4+c1+c6+c2
}
one sig rule10 extends Rule{}{
    s =s12
    t =r14
    m = prohibition
    p = 2
    c = c2+c4+c8
}
one sig rule11 extends Rule{}{
    s =s14
    t =r1
    m = permission
    p = 4
    c = c8+c3+c6+c1+c9
}
one sig rule12 extends Rule{}{
    s =s14
    t =r0
    m = permission
    p = 0
    c = c0+c3
}
one sig rule13 extends Rule{}{
    s =s1
    t =r9
    m = prohibition
    p = 1
    c = c1+c5+c6+c3+c0
}
one sig rule14 extends Rule{}{
    s =s12
    t =r10
    m = prohibition
    p = 3
    c = c9+c3+c2
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
