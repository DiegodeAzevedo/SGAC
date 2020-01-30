module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19 extends Subject{}{}
fact{
subSucc=s3->s1+
         s4->s1+
         s4->s3+
         s5->s1+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s5+
         s7->s2+
         s7->s4+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s4+
         s14->s6+
         s14->s10+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s9+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s8+
         s16->s9+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s15+
         s18->s3+
         s18->s4+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s13+
         s19->s18}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19 extends Resource{}{}
fact{
resSucc=r5->r1+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r4+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r5+
         r9->r1+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r6+
         r11->r7+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r4+
         r13->r5+
         r13->r8+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r7+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r11+
         r16->r0+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r12+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r7+
         r18->r10+
         r18->r11+
         r18->r13+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r14}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req8 extends Request{}{
sub=s1
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r7
    m = prohibition
    p = 0
    c = c4+c7+c2
}
one sig rule1 extends Rule{}{
    s =s4
    t =r3
    m = prohibition
    p = 4
    c = c2+c9+c5
}
one sig rule2 extends Rule{}{
    s =s14
    t =r19
    m = prohibition
    p = 2
    c = c5+c2+c8+c1+c6+c0+c7
}
one sig rule3 extends Rule{}{
    s =s0
    t =r9
    m = permission
    p = 1
    c = c9+c0+c3+c6+c4
}
one sig rule4 extends Rule{}{
    s =s10
    t =r0
    m = prohibition
    p = 2
    c = c0+c9+c2+c3+c6
}
one sig rule5 extends Rule{}{
    s =s18
    t =r16
    m = permission
    p = 3
    c = c5+c3+c2+c4+c0+c1+c8
}
one sig rule6 extends Rule{}{
    s =s8
    t =r13
    m = permission
    p = 4
    c = c9+c5+c1+c2+c4
}
one sig rule7 extends Rule{}{
    s =s4
    t =r14
    m = prohibition
    p = 3
    c = c6
}
one sig rule8 extends Rule{}{
    s =s15
    t =r3
    m = prohibition
    p = 2
    c = c6+c1+c2+c7+c0
}
one sig rule9 extends Rule{}{
    s =s5
    t =r2
    m = prohibition
    p = 2
    c = c6+c4
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
check HiddenDocument_r3_c0{ HiddenDocument[r3,c0]} for 4
check HiddenDocument_r3_c1{ HiddenDocument[r3,c1]} for 4
check HiddenDocument_r3_c2{ HiddenDocument[r3,c2]} for 4
check HiddenDocument_r3_c3{ HiddenDocument[r3,c3]} for 4
check HiddenDocument_r3_c4{ HiddenDocument[r3,c4]} for 4
check HiddenDocument_r3_c5{ HiddenDocument[r3,c5]} for 4
check HiddenDocument_r3_c6{ HiddenDocument[r3,c6]} for 4
check HiddenDocument_r3_c7{ HiddenDocument[r3,c7]} for 4
check HiddenDocument_r3_c8{ HiddenDocument[r3,c8]} for 4
check HiddenDocument_r3_c9{ HiddenDocument[r3,c9]} for 4
