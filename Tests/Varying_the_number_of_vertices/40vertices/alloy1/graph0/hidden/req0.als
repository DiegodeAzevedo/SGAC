module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s1+
         s6->s0+
         s6->s1+
         s7->s1+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s5+
         s9->s1+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s1+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s14->s1+
         s14->s5+
         s14->s6+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s5+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s2+
         s19->s3+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r5+
         r7->r1+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r3+
         r11->r5+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r2+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r16->r0+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r8+
         r18->r11+
         r18->r16+
         r19->r1+
         r19->r7+
         r19->r8+
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
    s =s14
    t =r2
    m = prohibition
    p = 4
    c = c9+c7+c1+c3+c6
}
one sig rule1 extends Rule{}{
    s =s18
    t =r15
    m = prohibition
    p = 4
    c = c8+c3+c5
}
one sig rule2 extends Rule{}{
    s =s5
    t =r7
    m = permission
    p = 0
    c = c3+c7+c5
}
one sig rule3 extends Rule{}{
    s =s4
    t =r0
    m = permission
    p = 3
    c = c0+c7+c5
}
one sig rule4 extends Rule{}{
    s =s1
    t =r5
    m = permission
    p = 0
    c = c7+c1+c4
}
one sig rule5 extends Rule{}{
    s =s12
    t =r4
    m = prohibition
    p = 4
    c = c0+c6+c4+c3
}
one sig rule6 extends Rule{}{
    s =s19
    t =r2
    m = permission
    p = 3
    c = c4
}
one sig rule7 extends Rule{}{
    s =s9
    t =r9
    m = permission
    p = 4
    c = c6+c3+c7+c9+c2+c0
}
one sig rule8 extends Rule{}{
    s =s1
    t =r17
    m = prohibition
    p = 2
    c = c3+c4+c7
}
one sig rule9 extends Rule{}{
    s =s12
    t =r14
    m = permission
    p = 3
    c = c8+c9
}
one sig rule10 extends Rule{}{
    s =s12
    t =r18
    m = prohibition
    p = 3
    c = c9+c5+c6+c8+c4
}
one sig rule11 extends Rule{}{
    s =s14
    t =r3
    m = permission
    p = 2
    c = c9+c8+c7+c2+c1
}
one sig rule12 extends Rule{}{
    s =s14
    t =r2
    m = prohibition
    p = 2
    c = c6+c1+c5+c7+c4+c0
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
