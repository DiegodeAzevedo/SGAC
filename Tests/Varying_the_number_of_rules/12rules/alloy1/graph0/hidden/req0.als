module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s6->s3+
         s6->s5+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s2+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s1+
         s11->s1+
         s11->s3+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s2+
         s12->s4+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s12+
         s15->s2+
         s15->s3+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s10+
         s18->s11+
         s18->s15+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r4->r1+
         r4->r2+
         r5->r2+
         r5->r3+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r9+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r7+
         r14->r9+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r7+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r4+
         r16->r7+
         r16->r10+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r3+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r13+
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
    s =s10
    t =r4
    m = permission
    p = 4
    c = c7+c9+c3+c6
}
one sig rule1 extends Rule{}{
    s =s10
    t =r16
    m = permission
    p = 4
    c = c9+c5+c6+c4+c0
}
one sig rule2 extends Rule{}{
    s =s7
    t =r15
    m = permission
    p = 0
    c = c7+c9+c2+c4+c5+c0
}
one sig rule3 extends Rule{}{
    s =s3
    t =r13
    m = permission
    p = 0
    c = c9+c8+c7+c3+c6
}
one sig rule4 extends Rule{}{
    s =s7
    t =r8
    m = permission
    p = 0
    c = c0+c2+c5+c7+c1+c8
}
one sig rule5 extends Rule{}{
    s =s13
    t =r17
    m = prohibition
    p = 1
    c = c8
}
one sig rule6 extends Rule{}{
    s =s17
    t =r3
    m = permission
    p = 0
    c = c2+c9+c0
}
one sig rule7 extends Rule{}{
    s =s2
    t =r17
    m = prohibition
    p = 3
    c = c5+c4+c3+c7+c8+c0+c9
}
one sig rule8 extends Rule{}{
    s =s14
    t =r16
    m = prohibition
    p = 2
    c = c8+c5+c4+c9+c3+c0+c1+c7
}
one sig rule9 extends Rule{}{
    s =s11
    t =r9
    m = prohibition
    p = 4
    c = c5+c1+c9+c4+c3
}
one sig rule10 extends Rule{}{
    s =s6
    t =r8
    m = prohibition
    p = 2
    c = c2+c8+c5+c9+c7
}
one sig rule11 extends Rule{}{
    s =s12
    t =r15
    m = permission
    p = 4
    c = c8+c6+c9+c0+c5
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
