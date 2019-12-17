module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s2+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s10+
         s12->s0+
         s12->s6+
         s12->s10+
         s12->s11+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s11+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s4+
         s16->s8+
         s16->s10+
         s16->s14+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s6+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s9+
         s18->s12+
         s18->s15+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r2+
         r5->r0+
         r5->r1+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r10+
         r15->r14+
         r16->r1+
         r16->r4+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r14+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r8+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s5
    t =r19
    m = permission
    p = 3
    c = c8+c2+c0+c4+c3+c6+c9+c7
}
one sig rule1 extends Rule{}{
    s =s14
    t =r5
    m = prohibition
    p = 3
    c = c5
}
one sig rule2 extends Rule{}{
    s =s17
    t =r19
    m = prohibition
    p = 4
    c = c1
}
one sig rule3 extends Rule{}{
    s =s14
    t =r8
    m = prohibition
    p = 4
    c = c6+c4+c9
}
one sig rule4 extends Rule{}{
    s =s2
    t =r5
    m = permission
    p = 1
    c = c8+c9+c1
}
one sig rule5 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 2
    c = c8+c7
}
one sig rule6 extends Rule{}{
    s =s15
    t =r9
    m = prohibition
    p = 3
    c = c8+c1+c6+c9+c3+c0+c5
}
one sig rule7 extends Rule{}{
    s =s14
    t =r8
    m = permission
    p = 1
    c = c5+c9+c8
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
