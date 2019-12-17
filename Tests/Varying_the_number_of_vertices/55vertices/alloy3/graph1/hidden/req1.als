module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s4->s3+
         s5->s0+
         s5->s2+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s10+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s13+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s15+
         s18->s0+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s5+
         s20->s7+
         s20->s9+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s18+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s17+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s18+
         s22->s19+
         s22->s20+
         s23->s4+
         s23->s9+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s19+
         s23->s21+
         s23->s22+
         s24->s1+
         s24->s2+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s14+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s6+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s16+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s20+
         s26->s23+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s23+
         s27->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r6+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r6+
         r14->r10+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r11+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r6+
         r17->r7+
         r17->r11+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r6+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r17+
         r19->r2+
         r19->r8+
         r19->r13+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r8+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r17+
         r21->r18+
         r22->r0+
         r22->r3+
         r22->r4+
         r22->r7+
         r22->r14+
         r22->r17+
         r22->r18+
         r22->r21+
         r23->r0+
         r23->r1+
         r23->r4+
         r23->r6+
         r23->r7+
         r23->r9+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r17+
         r23->r19+
         r24->r3+
         r24->r4+
         r24->r6+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r20+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r15+
         r25->r17+
         r25->r19+
         r25->r21+
         r25->r22+
         r26->r2+
         r26->r3+
         r26->r6+
         r26->r7+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r20+
         r26->r24}

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
    s =s21
    t =r5
    m = permission
    p = 3
    c = c1+c3+c5
}
one sig rule1 extends Rule{}{
    s =s2
    t =r5
    m = permission
    p = 4
    c = c2+c1+c9+c0+c8+c4+c6
}
one sig rule2 extends Rule{}{
    s =s18
    t =r9
    m = prohibition
    p = 4
    c = c0+c7+c2+c6+c5+c3+c4+c9
}
one sig rule3 extends Rule{}{
    s =s4
    t =r10
    m = permission
    p = 4
    c = c9+c5+c6
}
one sig rule4 extends Rule{}{
    s =s10
    t =r17
    m = permission
    p = 0
    c = c5+c7+c4+c3
}
one sig rule5 extends Rule{}{
    s =s0
    t =r11
    m = permission
    p = 0
    c = c6+c4+c9
}
one sig rule6 extends Rule{}{
    s =s5
    t =r22
    m = prohibition
    p = 3
    c = c9+c3+c8+c1+c0
}
one sig rule7 extends Rule{}{
    s =s4
    t =r14
    m = prohibition
    p = 1
    c = c2+c0+c4+c9
}
one sig rule8 extends Rule{}{
    s =s4
    t =r1
    m = permission
    p = 1
    c = c8+c6+c3
}
one sig rule9 extends Rule{}{
    s =s6
    t =r8
    m = permission
    p = 0
    c = c8+c2
}
one sig rule10 extends Rule{}{
    s =s11
    t =r8
    m = permission
    p = 2
    c = c8+c5+c6+c2+c7+c4
}
one sig rule11 extends Rule{}{
    s =s24
    t =r19
    m = prohibition
    p = 0
    c = c0+c4+c7
}
one sig rule12 extends Rule{}{
    s =s8
    t =r3
    m = prohibition
    p = 4
    c = c2+c0+c4+c7+c8
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
