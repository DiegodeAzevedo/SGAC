module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s2+
         s4->s1+
         s4->s2+
         s5->s1+
         s5->s4+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s5+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s7+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s8+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s12+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r5+
         r8->r0+
         r8->r3+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r3+
         r12->r7+
         r12->r9+
         r13->r1+
         r13->r3+
         r13->r7+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r6+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r14+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r14+
         r19->r1+
         r19->r4+
         r19->r10+
         r19->r14+
         r19->r16+
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
    s =s2
    t =r19
    m = permission
    p = 1
    c = c9+c4+c3+c6
}
one sig rule1 extends Rule{}{
    s =s9
    t =r1
    m = permission
    p = 4
    c = c0+c2+c4
}
one sig rule2 extends Rule{}{
    s =s4
    t =r10
    m = permission
    p = 4
    c = c3+c8+c7+c6+c0+c2
}
one sig rule3 extends Rule{}{
    s =s16
    t =r10
    m = permission
    p = 1
    c = c7+c0+c3+c6+c5+c8+c4+c2
}
one sig rule4 extends Rule{}{
    s =s13
    t =r17
    m = permission
    p = 3
    c = c6+c0+c4+c2+c1
}
one sig rule5 extends Rule{}{
    s =s8
    t =r7
    m = permission
    p = 0
    c = c8+c9+c3+c4+c1
}
one sig rule6 extends Rule{}{
    s =s12
    t =r7
    m = permission
    p = 2
    c = c3+c4+c7+c8+c2
}
one sig rule7 extends Rule{}{
    s =s5
    t =r19
    m = prohibition
    p = 2
    c = c0+c1
}
one sig rule8 extends Rule{}{
    s =s1
    t =r17
    m = permission
    p = 4
    c = c6+c0+c9+c8+c3+c7
}
one sig rule9 extends Rule{}{
    s =s16
    t =r2
    m = permission
    p = 4
    c = c0
}
one sig rule10 extends Rule{}{
    s =s12
    t =r14
    m = prohibition
    p = 1
    c = c2+c4+c9+c6+c0+c3+c8+c7
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
