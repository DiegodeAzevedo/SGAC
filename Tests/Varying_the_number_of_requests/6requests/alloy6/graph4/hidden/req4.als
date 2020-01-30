module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s3+
         s6->s1+
         s6->s5+
         s7->s1+
         s7->s2+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s7+
         s12->s8+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s6+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s12+
         s16->s14+
         s17->s0+
         s17->s1+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s13+
         s19->s14+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r4->r0+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r2+
         r11->r3+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r10+
         r13->r0+
         r13->r2+
         r13->r7+
         r13->r8+
         r13->r12+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r10+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r11+
         r17->r12+
         r18->r1+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r16+
         r19->r2+
         r19->r7+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r14
    m = permission
    p = 2
    c = c3+c4+c5+c1
}
one sig rule1 extends Rule{}{
    s =s5
    t =r7
    m = permission
    p = 3
    c = c5+c1+c9+c8+c3+c6+c2
}
one sig rule2 extends Rule{}{
    s =s16
    t =r13
    m = prohibition
    p = 1
    c = c3+c7+c0+c9
}
one sig rule3 extends Rule{}{
    s =s1
    t =r9
    m = prohibition
    p = 2
    c = c5
}
one sig rule4 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 3
    c = c2+c5
}
one sig rule5 extends Rule{}{
    s =s7
    t =r7
    m = prohibition
    p = 2
    c = c2+c7+c0+c5+c8+c4+c1
}
one sig rule6 extends Rule{}{
    s =s11
    t =r15
    m = prohibition
    p = 2
    c = c0+c8+c5+c1
}
one sig rule7 extends Rule{}{
    s =s1
    t =r1
    m = permission
    p = 4
    c = c0+c2+c9+c5+c7
}
one sig rule8 extends Rule{}{
    s =s13
    t =r7
    m = prohibition
    p = 4
    c = c5+c0
}
one sig rule9 extends Rule{}{
    s =s17
    t =r3
    m = prohibition
    p = 1
    c = c7+c9+c6
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
