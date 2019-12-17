module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22 extends Subject{}{}
fact{
subSucc=s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s1+
         s5->s0+
         s5->s3+
         s6->s2+
         s6->s3+
         s7->s2+
         s7->s4+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s8+
         s10->s3+
         s10->s5+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s9+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s4+
         s14->s6+
         s14->s8+
         s14->s9+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s4+
         s16->s6+
         s16->s7+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s11+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s5+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s15+
         s19->s17+
         s19->s18+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s5+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s13+
         s20->s15+
         s20->s16+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s20}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r1+
         r6->r0+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r4+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r5+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r5+
         r13->r7+
         r13->r9+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r9+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r14+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r16+
         r21->r20}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r0
    m = permission
    p = 2
    c = c4+c8+c5+c0+c3+c6
}
one sig rule1 extends Rule{}{
    s =s21
    t =r17
    m = prohibition
    p = 3
    c = c2+c9+c4+c5+c8
}
one sig rule2 extends Rule{}{
    s =s21
    t =r8
    m = prohibition
    p = 2
    c = c3+c4+c1+c5+c6+c2
}
one sig rule3 extends Rule{}{
    s =s9
    t =r16
    m = prohibition
    p = 0
    c = c5
}
one sig rule4 extends Rule{}{
    s =s13
    t =r20
    m = permission
    p = 4
    c = c7+c3+c8
}
one sig rule5 extends Rule{}{
    s =s0
    t =r19
    m = prohibition
    p = 4
    c = c4+c7+c3+c2+c5+c8
}
one sig rule6 extends Rule{}{
    s =s19
    t =r13
    m = prohibition
    p = 1
    c = c0+c5+c6+c9+c8
}
one sig rule7 extends Rule{}{
    s =s18
    t =r17
    m = permission
    p = 1
    c = c6+c7
}
one sig rule8 extends Rule{}{
    s =s2
    t =r16
    m = permission
    p = 4
    c = c1+c7+c5+c9+c2+c4+c6
}
one sig rule9 extends Rule{}{
    s =s15
    t =r11
    m = prohibition
    p = 4
    c = c9+c1+c6
}
one sig rule10 extends Rule{}{
    s =s15
    t =r13
    m = permission
    p = 0
    c = c6+c0+c5
}
one sig rule11 extends Rule{}{
    s =s1
    t =r4
    m = permission
    p = 3
    c = c7+c8+c5+c2+c3
}
one sig rule12 extends Rule{}{
    s =s21
    t =r16
    m = prohibition
    p = 2
    c = c0+c1+c7+c6+c3+c2
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
