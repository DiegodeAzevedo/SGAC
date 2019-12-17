module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s2+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s1+
         s9->s2+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s1+
         s12->s3+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s9+
         s13->s11+
         s14->s0+
         s14->s2+
         s14->s4+
         s14->s5+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s13+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s9+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s12+
         s17->s0+
         s17->s1+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s12+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s13+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s15+
         s19->s16+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s12+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s18+
         s21->s3+
         s21->s4+
         s21->s6+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s18+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s9+
         s22->s12+
         s22->s16+
         s22->s18+
         s22->s19}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r2+
         r9->r4+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r4+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r9+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r10+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r13+
         r17->r15+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r8+
         r18->r11+
         r18->r14+
         r18->r15+
         r19->r2+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r15+
         r20->r2+
         r20->r5+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r16+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r4+
         r21->r6+
         r21->r10+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r19}

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
    s =s6
    t =r1
    m = permission
    p = 1
    c = c6+c1+c5+c0+c8+c7
}
one sig rule1 extends Rule{}{
    s =s0
    t =r11
    m = permission
    p = 0
    c = c3+c7+c9+c4+c0+c2
}
one sig rule2 extends Rule{}{
    s =s20
    t =r6
    m = permission
    p = 4
    c = c6+c1+c4+c0+c9
}
one sig rule3 extends Rule{}{
    s =s8
    t =r0
    m = prohibition
    p = 1
    c = c0+c8+c2+c4+c5
}
one sig rule4 extends Rule{}{
    s =s15
    t =r13
    m = permission
    p = 2
    c = c2+c7+c4+c1+c3
}
one sig rule5 extends Rule{}{
    s =s18
    t =r1
    m = permission
    p = 1
    c = c1+c4+c2+c0+c3
}
one sig rule6 extends Rule{}{
    s =s7
    t =r13
    m = prohibition
    p = 3
    c = c4+c3+c5+c0+c2
}
one sig rule7 extends Rule{}{
    s =s13
    t =r20
    m = prohibition
    p = 4
    c = c1+c8+c6+c2+c0
}
one sig rule8 extends Rule{}{
    s =s11
    t =r16
    m = permission
    p = 3
    c = c3+c4+c1+c0+c8
}
one sig rule9 extends Rule{}{
    s =s0
    t =r14
    m = permission
    p = 4
    c = c9+c2+c7
}
one sig rule10 extends Rule{}{
    s =s0
    t =r15
    m = permission
    p = 4
    c = c4+c2+c5+c0+c7
}
one sig rule11 extends Rule{}{
    s =s13
    t =r4
    m = permission
    p = 4
    c = c0+c5+c3+c4
}
one sig rule12 extends Rule{}{
    s =s21
    t =r5
    m = permission
    p = 2
    c = c7+c1+c5+c6+c0+c9+c3
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
