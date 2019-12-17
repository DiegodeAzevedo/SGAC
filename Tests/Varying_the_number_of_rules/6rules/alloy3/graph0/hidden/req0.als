module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s3+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s11->s3+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s1+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s13+
         s16->s0+
         s16->s2+
         s16->s6+
         s16->s9+
         s16->s10+
         s16->s13+
         s16->s14+
         s17->s1+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s18->s1+
         s18->s4+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r3+
         r9->r4+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r8+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r11+
         r17->r15+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r10+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r13+
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
    s =s9
    t =r12
    m = permission
    p = 2
    c = c8+c6+c1+c5+c4+c3+c9+c0
}
one sig rule1 extends Rule{}{
    s =s15
    t =r3
    m = prohibition
    p = 1
    c = c5+c2+c9+c1+c0+c4
}
one sig rule2 extends Rule{}{
    s =s11
    t =r1
    m = permission
    p = 3
    c = c2+c6+c8+c7+c1
}
one sig rule3 extends Rule{}{
    s =s18
    t =r11
    m = permission
    p = 4
    c = c4
}
one sig rule4 extends Rule{}{
    s =s0
    t =r8
    m = prohibition
    p = 0
    c = c1+c6+c2+c0
}
one sig rule5 extends Rule{}{
    s =s5
    t =r4
    m = permission
    p = 1
    c = c0+c3
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
