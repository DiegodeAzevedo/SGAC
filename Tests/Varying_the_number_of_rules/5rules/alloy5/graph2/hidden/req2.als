module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s2+
         s4->s2+
         s5->s1+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s3+
         s12->s0+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s12+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s2+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s14+
         s18->s15+
         s19->s3+
         s19->s7+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s15}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r5+
         r7->r6+
         r8->r3+
         r8->r5+
         r9->r2+
         r9->r3+
         r9->r6+
         r9->r8+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r9+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r8+
         r13->r9+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r11+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r14+
         r17->r1+
         r17->r2+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r16+
         r19->r0+
         r19->r2+
         r19->r5+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r17+
         r19->r18}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r11
    m = permission
    p = 1
    c = c0+c9+c4+c3+c7
}
one sig rule1 extends Rule{}{
    s =s19
    t =r0
    m = prohibition
    p = 1
    c = c7
}
one sig rule2 extends Rule{}{
    s =s0
    t =r17
    m = prohibition
    p = 3
    c = c1+c0+c4+c2
}
one sig rule3 extends Rule{}{
    s =s5
    t =r7
    m = prohibition
    p = 3
    c = c4
}
one sig rule4 extends Rule{}{
    s =s0
    t =r15
    m = prohibition
    p = 1
    c = c7+c2
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
