module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s3+
         s5->s3+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s7+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s7+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s2+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s10+
         s13->s3+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s17+
         s19->s2+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r0+
         r6->r3+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r3+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r12->r0+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r13->r0+
         r13->r2+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r9+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r8+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r15+
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
    s =s19
    t =r10
    m = prohibition
    p = 0
    c = c1
}
one sig rule1 extends Rule{}{
    s =s18
    t =r3
    m = prohibition
    p = 3
    c = c3+c8+c0+c6+c4+c1
}
one sig rule2 extends Rule{}{
    s =s13
    t =r2
    m = permission
    p = 0
    c = c4+c2+c0+c6
}
one sig rule3 extends Rule{}{
    s =s15
    t =r15
    m = permission
    p = 1
    c = c0+c7+c9+c6+c4
}
one sig rule4 extends Rule{}{
    s =s11
    t =r18
    m = prohibition
    p = 0
    c = c5+c4+c3+c8
}
one sig rule5 extends Rule{}{
    s =s12
    t =r17
    m = permission
    p = 1
    c = c6+c8+c0+c7+c9+c2
}
one sig rule6 extends Rule{}{
    s =s18
    t =r12
    m = prohibition
    p = 3
    c = c1+c0+c3+c5
}
one sig rule7 extends Rule{}{
    s =s17
    t =r18
    m = permission
    p = 0
    c = c1+c7
}
one sig rule8 extends Rule{}{
    s =s9
    t =r19
    m = prohibition
    p = 2
    c = c3+c4+c7+c6+c0
}
one sig rule9 extends Rule{}{
    s =s11
    t =r17
    m = permission
    p = 3
    c = c9+c5+c1
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
