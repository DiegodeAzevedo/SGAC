module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s1+
         s10->s2+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s9+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s17->s1+
         s17->s4+
         s17->s6+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s5+
         s18->s6+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r4+
         r6->r5+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r5+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r6+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r3+
         r14->r9+
         r14->r10+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r6+
         r17->r8+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r15+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r18
    m = permission
    p = 0
    c = c5+c0+c6+c3+c7+c8
}
one sig rule1 extends Rule{}{
    s =s11
    t =r17
    m = prohibition
    p = 4
    c = c6+c0+c5+c9
}
one sig rule2 extends Rule{}{
    s =s0
    t =r5
    m = permission
    p = 2
    c = c1+c2+c4+c0+c8
}
one sig rule3 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 1
    c = c7+c2+c4
}
one sig rule4 extends Rule{}{
    s =s17
    t =r13
    m = permission
    p = 2
    c = c2+c0+c5+c3+c8+c4+c7
}
one sig rule5 extends Rule{}{
    s =s3
    t =r17
    m = permission
    p = 0
    c = c2+c4+c9+c6
}
one sig rule6 extends Rule{}{
    s =s10
    t =r5
    m = prohibition
    p = 3
    c = c2+c9+c1+c8+c0
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
