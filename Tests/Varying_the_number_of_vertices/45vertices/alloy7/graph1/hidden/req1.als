module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s1+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s0+
         s7->s2+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s2+
         s10->s3+
         s10->s4+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s12->s0+
         s12->s6+
         s12->s7+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s10+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s2+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s17->s0+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s6+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s20->s0+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s17+
         s21->s1+
         s21->s6+
         s21->s11+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s17+
         s22->s21}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r2+
         r4->r0+
         r4->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r3+
         r11->r7+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r11+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r6+
         r16->r7+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r11+
         r19->r0+
         r19->r3+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r17+
         r20->r1+
         r20->r2+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r17+
         r21->r20}

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
    s =s9
    t =r9
    m = permission
    p = 1
    c = c4+c8
}
one sig rule1 extends Rule{}{
    s =s10
    t =r14
    m = prohibition
    p = 3
    c = c4+c7+c2+c9+c5
}
one sig rule2 extends Rule{}{
    s =s16
    t =r9
    m = permission
    p = 0
    c = c3+c9+c6
}
one sig rule3 extends Rule{}{
    s =s7
    t =r19
    m = prohibition
    p = 1
    c = c7+c6+c4+c3
}
one sig rule4 extends Rule{}{
    s =s11
    t =r18
    m = prohibition
    p = 2
    c = c4+c3+c9+c1+c6
}
one sig rule5 extends Rule{}{
    s =s13
    t =r14
    m = prohibition
    p = 0
    c = c5+c7+c1
}
one sig rule6 extends Rule{}{
    s =s0
    t =r6
    m = prohibition
    p = 1
    c = c0+c8+c6+c5+c1+c2
}
one sig rule7 extends Rule{}{
    s =s11
    t =r4
    m = permission
    p = 4
    c = c8+c6+c1+c7
}
one sig rule8 extends Rule{}{
    s =s2
    t =r20
    m = prohibition
    p = 3
    c = c4+c7+c6
}
one sig rule9 extends Rule{}{
    s =s13
    t =r18
    m = prohibition
    p = 1
    c = c2+c7+c9+c3+c8+c4
}
one sig rule10 extends Rule{}{
    s =s12
    t =r10
    m = prohibition
    p = 1
    c = c6+c5+c3+c9+c2
}
one sig rule11 extends Rule{}{
    s =s21
    t =r0
    m = prohibition
    p = 3
    c = c0
}
one sig rule12 extends Rule{}{
    s =s14
    t =r19
    m = permission
    p = 4
    c = c4+c8+c6+c1+c0+c9+c5
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
