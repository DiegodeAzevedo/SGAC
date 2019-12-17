module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s2+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s7+
         s11->s0+
         s11->s5+
         s12->s3+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s7+
         s13->s9+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s7+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s4+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s7+
         s18->s9+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r5->r0+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r3+
         r6->r5+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r2+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r12+
         r16->r1+
         r16->r3+
         r16->r9+
         r16->r10+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r8+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r15+
         r19->r16}

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
    s =s16
    t =r8
    m = permission
    p = 1
    c = c7+c0+c1+c3+c8+c6
}
one sig rule1 extends Rule{}{
    s =s16
    t =r0
    m = prohibition
    p = 1
    c = c0
}
one sig rule2 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 0
    c = c3+c0+c2
}
one sig rule3 extends Rule{}{
    s =s6
    t =r6
    m = prohibition
    p = 2
    c = c2+c7+c0+c9+c5
}
one sig rule4 extends Rule{}{
    s =s4
    t =r14
    m = permission
    p = 3
    c = c7+c4+c6+c5+c0+c9+c8+c2
}
one sig rule5 extends Rule{}{
    s =s15
    t =r5
    m = prohibition
    p = 3
    c = c6+c7+c5+c2+c1
}
one sig rule6 extends Rule{}{
    s =s11
    t =r17
    m = permission
    p = 4
    c = c6+c2+c9+c3+c4+c1+c8
}
one sig rule7 extends Rule{}{
    s =s6
    t =r6
    m = permission
    p = 3
    c = c8
}
one sig rule8 extends Rule{}{
    s =s11
    t =r14
    m = permission
    p = 3
    c = c7+c8+c2
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
