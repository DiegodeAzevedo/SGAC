module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s7->s1+
         s7->s2+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s4+
         s13->s9+
         s13->s12+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s13+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s16+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s8+
         s19->s12+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r2+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r6+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r8+
         r13->r0+
         r13->r2+
         r13->r3+
         r13->r7+
         r13->r10+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r7+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r18->r1+
         r18->r3+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r9+
         r19->r10+
         r19->r12+
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
one sig req4 extends Request{}{
sub=s2
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s6
    t =r11
    m = permission
    p = 2
    c = c6+c2+c5+c3+c0+c8+c1
}
one sig rule1 extends Rule{}{
    s =s13
    t =r6
    m = permission
    p = 3
    c = c7+c0+c9+c1+c3+c5
}
one sig rule2 extends Rule{}{
    s =s4
    t =r2
    m = prohibition
    p = 2
    c = c7
}
one sig rule3 extends Rule{}{
    s =s12
    t =r14
    m = prohibition
    p = 0
    c = c5+c2+c4+c6
}
one sig rule4 extends Rule{}{
    s =s11
    t =r12
    m = prohibition
    p = 1
    c = c6+c8+c0+c7
}
one sig rule5 extends Rule{}{
    s =s0
    t =r11
    m = prohibition
    p = 2
    c = c6+c8+c3+c4+c1
}
one sig rule6 extends Rule{}{
    s =s0
    t =r11
    m = prohibition
    p = 3
    c = c3+c0+c5+c6+c1+c7+c2+c9
}
one sig rule7 extends Rule{}{
    s =s9
    t =r2
    m = permission
    p = 4
    c = c9+c8+c0
}
one sig rule8 extends Rule{}{
    s =s17
    t =r6
    m = permission
    p = 2
    c = c8+c6+c1+c0+c9+c3
}
one sig rule9 extends Rule{}{
    s =s12
    t =r4
    m = prohibition
    p = 4
    c = c7+c9+c5+c8+c2+c4+c1
}
one sig rule10 extends Rule{}{
    s =s10
    t =r9
    m = permission
    p = 4
    c = c2+c7+c9
}
one sig rule11 extends Rule{}{
    s =s12
    t =r15
    m = permission
    p = 2
    c = c0+c7+c4+c9+c1+c5
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
