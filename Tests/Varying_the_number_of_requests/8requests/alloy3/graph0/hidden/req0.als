module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s3+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s9+
         s11->s5+
         s11->s6+
         s12->s0+
         s12->s2+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s9+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s13+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s9+
         s18->s11+
         s18->s12+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r3+
         r6->r5+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r8+
         r10->r2+
         r10->r4+
         r11->r0+
         r11->r10+
         r12->r1+
         r12->r6+
         r12->r11+
         r13->r3+
         r13->r8+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r6+
         r14->r9+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r5+
         r18->r9+
         r18->r13+
         r18->r15+
         r19->r0+
         r19->r2+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r15+
         r19->r17}

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
    s =s0
    t =r9
    m = permission
    p = 1
    c = c7+c5+c0+c4
}
one sig rule1 extends Rule{}{
    s =s18
    t =r4
    m = permission
    p = 4
    c = c6+c8+c5+c3
}
one sig rule2 extends Rule{}{
    s =s4
    t =r17
    m = prohibition
    p = 0
    c = c9+c5+c8+c3
}
one sig rule3 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 3
    c = c3+c5+c2+c4+c1+c8
}
one sig rule4 extends Rule{}{
    s =s8
    t =r15
    m = permission
    p = 1
    c = c0+c8+c5+c2+c9+c1+c7
}
one sig rule5 extends Rule{}{
    s =s17
    t =r7
    m = permission
    p = 4
    c = c4+c5+c0+c8+c2
}
one sig rule6 extends Rule{}{
    s =s9
    t =r17
    m = permission
    p = 2
    c = c6+c8+c7+c5+c2+c4
}
one sig rule7 extends Rule{}{
    s =s9
    t =r2
    m = permission
    p = 0
    c = c3+c1+c9+c6+c0
}
one sig rule8 extends Rule{}{
    s =s9
    t =r3
    m = prohibition
    p = 1
    c = c5+c8
}
one sig rule9 extends Rule{}{
    s =s1
    t =r18
    m = prohibition
    p = 1
    c = c0+c3+c8+c9+c6
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
