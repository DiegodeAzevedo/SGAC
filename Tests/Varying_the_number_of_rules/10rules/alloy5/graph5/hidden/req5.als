module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s2+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s2+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s5+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s7+
         s13->s10+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s6+
         s15->s7+
         s15->s11+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s8+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s15+
         s18->s0+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r7->r1+
         r7->r2+
         r7->r3+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r8+
         r11->r1+
         r12->r0+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r3+
         r13->r6+
         r13->r7+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r14+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r4+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r13+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r6+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r2+
         r19->r3+
         r19->r7+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r15+
         r19->r16}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req5 extends Request{}{
sub=s2
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s2
    t =r17
    m = permission
    p = 2
    c = c6
}
one sig rule1 extends Rule{}{
    s =s11
    t =r13
    m = prohibition
    p = 2
    c = c7+c8+c4+c2
}
one sig rule2 extends Rule{}{
    s =s0
    t =r11
    m = prohibition
    p = 0
    c = c9+c4+c0+c6+c7
}
one sig rule3 extends Rule{}{
    s =s14
    t =r10
    m = permission
    p = 0
    c = c1+c4
}
one sig rule4 extends Rule{}{
    s =s8
    t =r9
    m = permission
    p = 3
    c = c0+c3+c6+c1+c9+c2
}
one sig rule5 extends Rule{}{
    s =s9
    t =r11
    m = prohibition
    p = 0
    c = c0
}
one sig rule6 extends Rule{}{
    s =s5
    t =r19
    m = permission
    p = 2
    c = c1+c0
}
one sig rule7 extends Rule{}{
    s =s5
    t =r11
    m = permission
    p = 4
    c = c1+c4+c3+c8+c9
}
one sig rule8 extends Rule{}{
    s =s8
    t =r3
    m = permission
    p = 0
    c = c4+c8+c1+c0+c3+c7+c6+c9
}
one sig rule9 extends Rule{}{
    s =s8
    t =r11
    m = permission
    p = 3
    c = c5+c4
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
check HiddenDocument_r3_c0{ HiddenDocument[r3,c0]} for 4
check HiddenDocument_r3_c1{ HiddenDocument[r3,c1]} for 4
check HiddenDocument_r3_c2{ HiddenDocument[r3,c2]} for 4
check HiddenDocument_r3_c3{ HiddenDocument[r3,c3]} for 4
check HiddenDocument_r3_c4{ HiddenDocument[r3,c4]} for 4
check HiddenDocument_r3_c5{ HiddenDocument[r3,c5]} for 4
check HiddenDocument_r3_c6{ HiddenDocument[r3,c6]} for 4
check HiddenDocument_r3_c7{ HiddenDocument[r3,c7]} for 4
check HiddenDocument_r3_c8{ HiddenDocument[r3,c8]} for 4
check HiddenDocument_r3_c9{ HiddenDocument[r3,c9]} for 4
