module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s1+
         s7->s0+
         s7->s2+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s8+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s10+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s11+
         s13->s12+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s9+
         s14->s13+
         s15->s0+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s19->s1+
         s19->s8+
         s19->s11+
         s19->s13+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r1+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r2+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r3+
         r7->r4+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r7+
         r12->r9+
         r13->r2+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r12+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r4+
         r15->r8+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r12+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r4+
         r18->r5+
         r18->r10+
         r18->r12+
         r18->r14+
         r18->r16+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r12+
         r19->r13+
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
one sig req3 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s13
    t =r8
    m = prohibition
    p = 3
    c = c2+c7
}
one sig rule1 extends Rule{}{
    s =s3
    t =r14
    m = prohibition
    p = 0
    c = c1+c7+c6
}
one sig rule2 extends Rule{}{
    s =s4
    t =r14
    m = permission
    p = 4
    c = c2+c8+c0+c3+c7
}
one sig rule3 extends Rule{}{
    s =s19
    t =r3
    m = prohibition
    p = 0
    c = c3+c4+c5
}
one sig rule4 extends Rule{}{
    s =s3
    t =r9
    m = permission
    p = 2
    c = c7+c2+c1+c3
}
one sig rule5 extends Rule{}{
    s =s15
    t =r16
    m = prohibition
    p = 0
    c = c4+c0+c8+c7+c6+c5
}
one sig rule6 extends Rule{}{
    s =s15
    t =r7
    m = permission
    p = 1
    c = c5+c3
}
one sig rule7 extends Rule{}{
    s =s1
    t =r2
    m = prohibition
    p = 0
    c = c5+c9+c8+c0+c2+c1+c4+c6
}
one sig rule8 extends Rule{}{
    s =s0
    t =r12
    m = permission
    p = 4
    c = c7+c6+c4+c5+c9+c3
}
one sig rule9 extends Rule{}{
    s =s17
    t =r9
    m = prohibition
    p = 0
    c = c0+c4+c7+c1+c3+c5
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
