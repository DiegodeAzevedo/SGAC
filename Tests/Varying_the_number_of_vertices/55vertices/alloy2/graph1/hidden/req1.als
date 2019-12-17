module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s1+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s10+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s3+
         s19->s4+
         s19->s6+
         s19->s7+
         s19->s12+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s7+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s2+
         s21->s4+
         s21->s6+
         s21->s7+
         s21->s12+
         s21->s13+
         s22->s0+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s23->s4+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s20+
         s24->s2+
         s24->s6+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s16+
         s24->s18+
         s24->s20+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s15+
         s25->s19+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s23+
         s27->s1+
         s27->s3+
         s27->s5+
         s27->s7+
         s27->s8+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s19+
         s27->s21+
         s27->s24}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r3+
         r7->r1+
         r7->r4+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r4+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r6+
         r12->r9+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r10+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r8+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r19->r0+
         r19->r2+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r6+
         r21->r8+
         r21->r12+
         r21->r15+
         r21->r16+
         r21->r19+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r7+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r23->r0+
         r23->r1+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r7+
         r24->r8+
         r24->r11+
         r24->r13+
         r24->r14+
         r24->r22+
         r25->r0+
         r25->r2+
         r25->r5+
         r25->r9+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r19+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r25}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s8
    t =r26
    m = prohibition
    p = 2
    c = c7+c6+c8+c5+c3+c2
}
one sig rule1 extends Rule{}{
    s =s5
    t =r23
    m = permission
    p = 1
    c = c2+c0
}
one sig rule2 extends Rule{}{
    s =s21
    t =r26
    m = prohibition
    p = 1
    c = c3
}
one sig rule3 extends Rule{}{
    s =s10
    t =r26
    m = permission
    p = 2
    c = c9+c1+c4+c2+c7+c5
}
one sig rule4 extends Rule{}{
    s =s22
    t =r24
    m = prohibition
    p = 0
    c = c7+c9+c2+c0+c6
}
one sig rule5 extends Rule{}{
    s =s11
    t =r5
    m = permission
    p = 0
    c = c2+c5+c6+c1+c9+c7+c0+c3
}
one sig rule6 extends Rule{}{
    s =s21
    t =r16
    m = permission
    p = 0
    c = c3+c1+c0+c9+c7+c2
}
one sig rule7 extends Rule{}{
    s =s12
    t =r16
    m = prohibition
    p = 4
    c = c8+c7
}
one sig rule8 extends Rule{}{
    s =s19
    t =r25
    m = permission
    p = 1
    c = c9+c8+c7+c2+c0
}
one sig rule9 extends Rule{}{
    s =s7
    t =r21
    m = permission
    p = 2
    c = c8+c5+c7+c0+c4+c2
}
one sig rule10 extends Rule{}{
    s =s12
    t =r6
    m = prohibition
    p = 0
    c = c8+c3+c7+c4+c2
}
one sig rule11 extends Rule{}{
    s =s13
    t =r8
    m = prohibition
    p = 3
    c = c2+c3+c6+c5+c4
}
one sig rule12 extends Rule{}{
    s =s24
    t =r8
    m = permission
    p = 2
    c = c6+c2+c7
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
