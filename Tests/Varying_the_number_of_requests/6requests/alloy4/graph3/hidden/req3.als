module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s2+
         s4->s1+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s4+
         s6->s5+
         s7->s2+
         s8->s0+
         s8->s1+
         s8->s2+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s3+
         s11->s8+
         s12->s0+
         s12->s2+
         s12->s8+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s9+
         s13->s11+
         s14->s1+
         s14->s4+
         s14->s9+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s8+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s8}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r3+
         r11->r4+
         r11->r7+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r5+
         r12->r7+
         r12->r10+
         r13->r0+
         r13->r3+
         r13->r5+
         r13->r8+
         r13->r9+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r4+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r12+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r12+
         r19->r13+
         r19->r16+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s13
    t =r6
    m = permission
    p = 2
    c = c6+c7+c3+c4
}
one sig rule1 extends Rule{}{
    s =s5
    t =r9
    m = permission
    p = 4
    c = c3+c7+c6
}
one sig rule2 extends Rule{}{
    s =s19
    t =r11
    m = prohibition
    p = 2
    c = c2+c5+c1+c0+c7+c9+c3+c6
}
one sig rule3 extends Rule{}{
    s =s19
    t =r14
    m = permission
    p = 3
    c = c0+c9+c5+c6
}
one sig rule4 extends Rule{}{
    s =s8
    t =r14
    m = prohibition
    p = 4
    c = c1+c0+c9+c2+c6
}
one sig rule5 extends Rule{}{
    s =s2
    t =r2
    m = permission
    p = 3
    c = c6
}
one sig rule6 extends Rule{}{
    s =s19
    t =r2
    m = permission
    p = 2
    c = c3
}
one sig rule7 extends Rule{}{
    s =s19
    t =r14
    m = permission
    p = 3
    c = c1+c2+c0+c5+c4+c6
}
one sig rule8 extends Rule{}{
    s =s4
    t =r16
    m = permission
    p = 3
    c = c3+c7+c1
}
one sig rule9 extends Rule{}{
    s =s11
    t =r17
    m = permission
    p = 1
    c = c6+c8+c4
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
