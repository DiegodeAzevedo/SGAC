module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s1+
         s4->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s3+
         s6->s4+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s3+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s6+
         s10->s7+
         s11->s2+
         s11->s3+
         s11->s6+
         s11->s8+
         s11->s10+
         s12->s3+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s6+
         s13->s9+
         s14->s4+
         s14->s7+
         s14->s8+
         s14->s11+
         s15->s2+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s7+
         s16->s8+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s8+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s13+
         s19->s16}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r9->r0+
         r9->r2+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r4+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r10+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r11+
         r14->r5+
         r14->r7+
         r14->r9+
         r14->r10+
         r15->r7+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r9+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r3+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r17+
         r19->r18}

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
    s =s0
    t =r0
    m = permission
    p = 0
    c = c8+c9+c6
}
one sig rule1 extends Rule{}{
    s =s3
    t =r7
    m = prohibition
    p = 2
    c = c4+c2+c5+c8+c3
}
one sig rule2 extends Rule{}{
    s =s5
    t =r5
    m = prohibition
    p = 2
    c = c4+c5+c2+c6+c8+c7
}
one sig rule3 extends Rule{}{
    s =s13
    t =r7
    m = prohibition
    p = 0
    c = c9+c1+c2+c4+c7+c0+c8
}
one sig rule4 extends Rule{}{
    s =s16
    t =r19
    m = permission
    p = 0
    c = c5
}
one sig rule5 extends Rule{}{
    s =s7
    t =r0
    m = permission
    p = 3
    c = c7+c5+c3+c9+c4+c0
}
one sig rule6 extends Rule{}{
    s =s7
    t =r15
    m = permission
    p = 3
    c = c6+c4+c2+c9+c7+c5+c0+c8+c3
}
one sig rule7 extends Rule{}{
    s =s18
    t =r2
    m = permission
    p = 2
    c = c4
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
