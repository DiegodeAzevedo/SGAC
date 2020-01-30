module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s2+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s10+
         s12->s5+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s8+
         s13->s11+
         s14->s0+
         s14->s5+
         s14->s9+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s7+
         s18->s10+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s10+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r2+
         r7->r3+
         r8->r0+
         r8->r1+
         r8->r6+
         r9->r1+
         r9->r4+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r5+
         r11->r1+
         r11->r2+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r10+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r13+
         r15->r2+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r11+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s12
    t =r13
    m = permission
    p = 0
    c = c4+c6+c5+c9+c0+c2
}
one sig rule1 extends Rule{}{
    s =s9
    t =r17
    m = permission
    p = 1
    c = c1+c3+c6
}
one sig rule2 extends Rule{}{
    s =s0
    t =r19
    m = prohibition
    p = 2
    c = c5+c4
}
one sig rule3 extends Rule{}{
    s =s17
    t =r19
    m = prohibition
    p = 4
    c = c3+c6+c0+c1+c8
}
one sig rule4 extends Rule{}{
    s =s10
    t =r13
    m = permission
    p = 3
    c = c2+c8+c7+c5+c1+c4+c0
}
one sig rule5 extends Rule{}{
    s =s3
    t =r14
    m = permission
    p = 3
    c = c8
}
one sig rule6 extends Rule{}{
    s =s3
    t =r8
    m = prohibition
    p = 2
    c = c4+c3+c6+c9+c1+c5
}
one sig rule7 extends Rule{}{
    s =s10
    t =r12
    m = prohibition
    p = 3
    c = c2+c0+c6
}
one sig rule8 extends Rule{}{
    s =s11
    t =r17
    m = prohibition
    p = 4
    c = c0+c8
}
one sig rule9 extends Rule{}{
    s =s18
    t =r1
    m = permission
    p = 0
    c = c3
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
