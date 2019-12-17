module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s3+
         s6->s4+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s5+
         s9->s1+
         s9->s4+
         s9->s5+
         s10->s3+
         s10->s5+
         s10->s9+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s10+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s8+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s16->s1+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s17->s0+
         s17->s2+
         s17->s5+
         s17->s6+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s3+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s16+
         s18->s17+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s8+
         s19->s9+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s8+
         s20->s9+
         s20->s13+
         s20->s14+
         s20->s19+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s8+
         s22->s10+
         s22->s14+
         s22->s16+
         s22->s18+
         s22->s19+
         s22->s20+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s20+
         s23->s22+
         s24->s3+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s22+
         s25->s3+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s22+
         s26->s0+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s21+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s2+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s10+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s25+
         s27->s26+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s8+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s22+
         s28->s23+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s6+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r4->r2+
         r4->r3+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r3+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r3+
         r14->r7+
         r14->r8+
         r14->r10+
         r15->r2+
         r15->r6+
         r15->r9+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r7+
         r17->r11+
         r17->r13+
         r18->r3+
         r18->r5+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r15+
         r20->r18+
         r21->r0+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r11+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r19+
         r22->r1+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r16+
         r22->r19+
         r22->r20+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r6+
         r23->r9+
         r23->r13+
         r23->r16+
         r23->r17+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r2+
         r24->r3+
         r24->r6+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r14+
         r24->r20+
         r24->r22+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r13+
         r25->r14+
         r25->r17+
         r25->r20+
         r25->r23+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r5+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r11+
         r26->r14+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r25+
         r27->r1+
         r27->r5+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r5+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r7+
         r29->r9+
         r29->r10+
         r29->r12+
         r29->r14+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r25+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r8
    m = permission
    p = 3
    c = c3+c8+c1+c9
}
one sig rule1 extends Rule{}{
    s =s22
    t =r11
    m = prohibition
    p = 2
    c = c5+c0+c6+c9
}
one sig rule2 extends Rule{}{
    s =s24
    t =r26
    m = prohibition
    p = 0
    c = c6+c3+c1+c9
}
one sig rule3 extends Rule{}{
    s =s10
    t =r5
    m = prohibition
    p = 3
    c = c0+c2+c5+c7+c6+c4
}
one sig rule4 extends Rule{}{
    s =s15
    t =r17
    m = prohibition
    p = 2
    c = c7+c6+c8
}
one sig rule5 extends Rule{}{
    s =s1
    t =r27
    m = permission
    p = 0
    c = c7+c6+c4+c0+c1
}
one sig rule6 extends Rule{}{
    s =s3
    t =r14
    m = prohibition
    p = 2
    c = c1+c5+c7+c0+c3
}
one sig rule7 extends Rule{}{
    s =s10
    t =r20
    m = permission
    p = 2
    c = c4+c6+c0+c1
}
one sig rule8 extends Rule{}{
    s =s5
    t =r24
    m = permission
    p = 0
    c = c3+c2+c7+c9
}
one sig rule9 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 4
    c = c6+c1+c4
}
one sig rule10 extends Rule{}{
    s =s7
    t =r1
    m = prohibition
    p = 1
    c = c5+c4+c7+c0
}
one sig rule11 extends Rule{}{
    s =s0
    t =r13
    m = permission
    p = 3
    c = c7+c4+c3+c1+c9+c6+c8
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
check HiddenDocument_r2_c0{ HiddenDocument[r2,c0]} for 4
check HiddenDocument_r2_c1{ HiddenDocument[r2,c1]} for 4
check HiddenDocument_r2_c2{ HiddenDocument[r2,c2]} for 4
check HiddenDocument_r2_c3{ HiddenDocument[r2,c3]} for 4
check HiddenDocument_r2_c4{ HiddenDocument[r2,c4]} for 4
check HiddenDocument_r2_c5{ HiddenDocument[r2,c5]} for 4
check HiddenDocument_r2_c6{ HiddenDocument[r2,c6]} for 4
check HiddenDocument_r2_c7{ HiddenDocument[r2,c7]} for 4
check HiddenDocument_r2_c8{ HiddenDocument[r2,c8]} for 4
check HiddenDocument_r2_c9{ HiddenDocument[r2,c9]} for 4
