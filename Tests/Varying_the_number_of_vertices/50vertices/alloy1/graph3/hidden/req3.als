module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s1+
         s7->s4+
         s7->s5+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s1+
         s9->s6+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s8+
         s11->s9+
         s12->s2+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s5+
         s13->s9+
         s13->s11+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s10+
         s14->s11+
         s15->s0+
         s15->s1+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s3+
         s16->s6+
         s16->s11+
         s16->s15+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s9+
         s18->s13+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s9+
         s20->s10+
         s20->s14+
         s20->s16+
         s20->s18+
         s20->s19+
         s21->s2+
         s21->s6+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s14+
         s21->s19+
         s21->s20+
         s22->s2+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s12+
         s23->s13+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s15+
         s24->s16+
         s24->s21+
         s24->s23}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r5->r1+
         r5->r2+
         r6->r2+
         r7->r1+
         r7->r4+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r9+
         r13->r7+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r6+
         r14->r8+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r12+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r4+
         r18->r5+
         r18->r8+
         r18->r11+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r15+
         r19->r18+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r9+
         r20->r10+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r18+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r19+
         r23->r0+
         r23->r1+
         r23->r3+
         r23->r5+
         r23->r7+
         r23->r14+
         r23->r16+
         r23->r18+
         r23->r19+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r18+
         r24->r21}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r4
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s9
    t =r13
    m = permission
    p = 4
    c = c3+c2
}
one sig rule1 extends Rule{}{
    s =s10
    t =r16
    m = permission
    p = 1
    c = c0+c2+c7+c6+c1+c9+c5
}
one sig rule2 extends Rule{}{
    s =s13
    t =r21
    m = permission
    p = 1
    c = c7+c6+c2+c4
}
one sig rule3 extends Rule{}{
    s =s21
    t =r14
    m = permission
    p = 1
    c = c1+c9+c8+c3
}
one sig rule4 extends Rule{}{
    s =s11
    t =r13
    m = permission
    p = 0
    c = c1+c9+c5+c4
}
one sig rule5 extends Rule{}{
    s =s13
    t =r4
    m = prohibition
    p = 4
    c = c8
}
one sig rule6 extends Rule{}{
    s =s14
    t =r3
    m = permission
    p = 2
    c = c2+c7+c9
}
one sig rule7 extends Rule{}{
    s =s3
    t =r13
    m = prohibition
    p = 1
    c = c4+c6+c8
}
one sig rule8 extends Rule{}{
    s =s18
    t =r10
    m = prohibition
    p = 2
    c = c3+c4+c6+c1+c8+c7
}
one sig rule9 extends Rule{}{
    s =s17
    t =r10
    m = prohibition
    p = 0
    c = c6
}
one sig rule10 extends Rule{}{
    s =s2
    t =r9
    m = permission
    p = 0
    c = c9+c3+c5+c2+c0+c4
}
one sig rule11 extends Rule{}{
    s =s11
    t =r7
    m = permission
    p = 1
    c = c7+c8+c5+c4+c6+c1
}
one sig rule12 extends Rule{}{
    s =s5
    t =r8
    m = permission
    p = 2
    c = c9+c8+c7+c1+c6+c5+c4
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
check HiddenDocument_r4_c0{ HiddenDocument[r4,c0]} for 4
check HiddenDocument_r4_c1{ HiddenDocument[r4,c1]} for 4
check HiddenDocument_r4_c2{ HiddenDocument[r4,c2]} for 4
check HiddenDocument_r4_c3{ HiddenDocument[r4,c3]} for 4
check HiddenDocument_r4_c4{ HiddenDocument[r4,c4]} for 4
check HiddenDocument_r4_c5{ HiddenDocument[r4,c5]} for 4
check HiddenDocument_r4_c6{ HiddenDocument[r4,c6]} for 4
check HiddenDocument_r4_c7{ HiddenDocument[r4,c7]} for 4
check HiddenDocument_r4_c8{ HiddenDocument[r4,c8]} for 4
check HiddenDocument_r4_c9{ HiddenDocument[r4,c9]} for 4
