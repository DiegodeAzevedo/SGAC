module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s2+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s5+
         s9->s8+
         s10->s2+
         s10->s8+
         s11->s1+
         s11->s7+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s7+
         s13->s8+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s13+
         s15->s3+
         s15->s4+
         s15->s7+
         s15->s9+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s4+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s5+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s14+
         s20->s1+
         s20->s3+
         s20->s4+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s14+
         s20->s15+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s4+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s16+
         s21->s18+
         s21->s19+
         s22->s1+
         s22->s2+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s12+
         s22->s16+
         s22->s17+
         s22->s21+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s7+
         s23->s8+
         s23->s15+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s25->s1+
         s25->s3+
         s25->s4+
         s25->s6+
         s25->s7+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s22+
         s25->s23+
         s26->s1+
         s26->s2+
         s26->s5+
         s26->s6+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s16+
         s26->s18+
         s26->s20+
         s26->s22+
         s26->s24+
         s27->s1+
         s27->s3+
         s27->s6+
         s27->s7+
         s27->s10+
         s27->s11+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s20+
         s27->s24+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s18+
         s28->s21+
         s28->s22+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s10+
         s29->s17+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r0+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r6+
         r8->r2+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r0+
         r10->r2+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r5+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r6+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r5+
         r13->r6+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r3+
         r14->r8+
         r14->r9+
         r14->r10+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r11+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r9+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r4+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r12+
         r19->r16+
         r19->r17+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r4+
         r21->r5+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r9+
         r22->r10+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r3+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r18+
         r24->r19+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r11+
         r25->r14+
         r25->r15+
         r25->r18+
         r25->r20+
         r25->r23+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r11+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r5+
         r27->r6+
         r27->r9+
         r27->r12+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r22+
         r27->r24+
         r27->r26+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r10+
         r28->r12+
         r28->r14+
         r28->r16+
         r28->r17+
         r28->r19+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r27+
         r29->r2+
         r29->r4+
         r29->r6+
         r29->r10+
         r29->r12+
         r29->r14+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r26+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s15
    t =r25
    m = prohibition
    p = 4
    c = c15+c6+c0+c3+c1+c4+c9+c17+c11+c14+c12+c16
}
one sig rule1 extends Rule{}{
    s =s2
    t =r11
    m = prohibition
    p = 4
    c = c1+c18+c2+c12+c0+c6+c9+c19+c5+c11
}
one sig rule2 extends Rule{}{
    s =s28
    t =r25
    m = permission
    p = 0
    c = c6+c9+c10+c2+c18+c12+c16+c1+c0+c17+c19+c14+c7+c15
}
one sig rule3 extends Rule{}{
    s =s3
    t =r11
    m = permission
    p = 3
    c = c7+c15+c18+c4+c5+c16+c12
}
one sig rule4 extends Rule{}{
    s =s0
    t =r22
    m = prohibition
    p = 4
    c = c19+c5+c18+c1+c0+c14+c2+c7+c6
}
one sig rule5 extends Rule{}{
    s =s21
    t =r15
    m = permission
    p = 4
    c = c11+c6+c9+c10+c12+c17+c13+c5+c8+c14
}
one sig rule6 extends Rule{}{
    s =s5
    t =r9
    m = permission
    p = 3
    c = c0+c18+c4+c6+c17+c9
}
one sig rule7 extends Rule{}{
    s =s20
    t =r29
    m = permission
    p = 0
    c = c16+c0+c11+c3+c17+c7+c19+c13+c4+c10+c14
}
one sig rule8 extends Rule{}{
    s =s3
    t =r13
    m = prohibition
    p = 2
    c = c0+c8+c6+c12+c9+c2+c16+c5+c7+c19+c10+c15
}
one sig rule9 extends Rule{}{
    s =s12
    t =r27
    m = permission
    p = 0
    c = c14
}
one sig rule10 extends Rule{}{
    s =s16
    t =r2
    m = prohibition
    p = 3
    c = c2+c3+c16+c13+c17+c9+c0+c11+c19+c18+c14
}
one sig rule11 extends Rule{}{
    s =s8
    t =r2
    m = prohibition
    p = 1
    c = c7+c4+c6+c3+c12+c9+c17+c0+c18+c1
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
check HiddenDocument_r3_c10{ HiddenDocument[r3,c10]} for 4
check HiddenDocument_r3_c11{ HiddenDocument[r3,c11]} for 4
check HiddenDocument_r3_c12{ HiddenDocument[r3,c12]} for 4
check HiddenDocument_r3_c13{ HiddenDocument[r3,c13]} for 4
check HiddenDocument_r3_c14{ HiddenDocument[r3,c14]} for 4
check HiddenDocument_r3_c15{ HiddenDocument[r3,c15]} for 4
check HiddenDocument_r3_c16{ HiddenDocument[r3,c16]} for 4
check HiddenDocument_r3_c17{ HiddenDocument[r3,c17]} for 4
check HiddenDocument_r3_c18{ HiddenDocument[r3,c18]} for 4
check HiddenDocument_r3_c19{ HiddenDocument[r3,c19]} for 4
