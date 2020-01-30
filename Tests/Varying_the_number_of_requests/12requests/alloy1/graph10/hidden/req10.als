module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s5->s0+
         s6->s0+
         s6->s1+
         s7->s2+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s10+
         s12->s3+
         s12->s4+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s7+
         s13->s8+
         s13->s11+
         s14->s1+
         s14->s4+
         s14->s7+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s9+
         s16->s10+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s13+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r2+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r2+
         r7->r0+
         r7->r2+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r5+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r3+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r8+
         r12->r9+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r3+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r13+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r11+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r15+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req10 extends Request{}{
sub=s4
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s11
    t =r11
    m = permission
    p = 3
    c = c5+c4+c6+c3+c2
}
one sig rule1 extends Rule{}{
    s =s3
    t =r6
    m = prohibition
    p = 4
    c = c8+c2+c9+c7+c5
}
one sig rule2 extends Rule{}{
    s =s3
    t =r13
    m = permission
    p = 3
    c = c3+c9+c1
}
one sig rule3 extends Rule{}{
    s =s2
    t =r7
    m = permission
    p = 4
    c = c9+c6+c3+c7+c1
}
one sig rule4 extends Rule{}{
    s =s17
    t =r11
    m = permission
    p = 4
    c = c6+c0+c9+c2+c3
}
one sig rule5 extends Rule{}{
    s =s17
    t =r4
    m = prohibition
    p = 0
    c = c5
}
one sig rule6 extends Rule{}{
    s =s1
    t =r6
    m = permission
    p = 3
    c = c2
}
one sig rule7 extends Rule{}{
    s =s4
    t =r8
    m = permission
    p = 0
    c = c6+c4+c8+c7
}
one sig rule8 extends Rule{}{
    s =s8
    t =r9
    m = permission
    p = 0
    c = c9+c4+c0
}
one sig rule9 extends Rule{}{
    s =s3
    t =r8
    m = permission
    p = 0
    c = c5+c0
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
