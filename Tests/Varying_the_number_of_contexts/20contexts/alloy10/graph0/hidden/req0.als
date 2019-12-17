module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s1+
         s6->s2+
         s7->s0+
         s7->s2+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s3+
         s8->s4+
         s8->s5+
         s9->s2+
         s9->s3+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s1+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s6+
         s14->s9+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s6+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s16+
         s18->s1+
         s18->s4+
         s18->s7+
         s18->s8+
         s18->s11+
         s18->s15+
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
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s2+
         s20->s6+
         s20->s8+
         s20->s10+
         s20->s12+
         s20->s18+
         s20->s19+
         s21->s5+
         s21->s8+
         s21->s12+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s12+
         s22->s14+
         s22->s15+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s13+
         s23->s15+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s4+
         s24->s5+
         s24->s12+
         s24->s15+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s2+
         s25->s3+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s19+
         s25->s20+
         s26->s3+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s14+
         s27->s17+
         s27->s18+
         s27->s21+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s8+
         s28->s13+
         s28->s15+
         s28->s19+
         s28->s26+
         s28->s27+
         s29->s6+
         s29->s7+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s21+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r0+
         r5->r2+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r3+
         r8->r0+
         r8->r3+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r11+
         r15->r14+
         r16->r0+
         r16->r5+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r11+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r12+
         r20->r15+
         r20->r16+
         r20->r17+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r13+
         r21->r16+
         r21->r18+
         r22->r0+
         r22->r1+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r17+
         r22->r18+
         r22->r20+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r12+
         r23->r14+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r6+
         r24->r9+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r19+
         r24->r21+
         r24->r22+
         r25->r1+
         r25->r2+
         r25->r5+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r13+
         r25->r18+
         r25->r19+
         r25->r21+
         r25->r22+
         r26->r0+
         r26->r5+
         r26->r7+
         r26->r10+
         r26->r11+
         r26->r13+
         r26->r16+
         r26->r17+
         r26->r19+
         r26->r20+
         r26->r21+
         r27->r1+
         r27->r2+
         r27->r6+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r13+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r9+
         r28->r10+
         r28->r12+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r23+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r16+
         r29->r22+
         r29->r23+
         r29->r25+
         r29->r26+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19 extends Context{}{}

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
    s =s2
    t =r4
    m = prohibition
    p = 1
    c = c14+c7+c10
}
one sig rule1 extends Rule{}{
    s =s19
    t =r21
    m = prohibition
    p = 1
    c = c18+c14+c5+c13+c3+c1+c16
}
one sig rule2 extends Rule{}{
    s =s2
    t =r25
    m = permission
    p = 2
    c = c8+c9+c5+c19+c0+c7+c6
}
one sig rule3 extends Rule{}{
    s =s21
    t =r18
    m = permission
    p = 4
    c = c0+c1+c15+c14+c11+c2+c10+c8+c18+c17+c9+c4+c6
}
one sig rule4 extends Rule{}{
    s =s25
    t =r16
    m = prohibition
    p = 0
    c = c2+c15+c0
}
one sig rule5 extends Rule{}{
    s =s0
    t =r23
    m = permission
    p = 0
    c = c4+c0+c14+c9+c1
}
one sig rule6 extends Rule{}{
    s =s12
    t =r18
    m = prohibition
    p = 2
    c = c10+c13
}
one sig rule7 extends Rule{}{
    s =s7
    t =r22
    m = prohibition
    p = 4
    c = c11+c3+c6+c16+c4+c5+c9+c10+c1+c13+c15+c8
}
one sig rule8 extends Rule{}{
    s =s26
    t =r15
    m = permission
    p = 2
    c = c9+c11+c10+c0+c14+c8+c2+c12+c18
}
one sig rule9 extends Rule{}{
    s =s20
    t =r11
    m = prohibition
    p = 3
    c = c14+c9+c16+c6+c2+c1+c3+c11+c5+c4+c12+c0
}
one sig rule10 extends Rule{}{
    s =s12
    t =r4
    m = permission
    p = 3
    c = c14+c15+c12+c0+c6+c2+c17+c13+c8+c10
}
one sig rule11 extends Rule{}{
    s =s17
    t =r13
    m = permission
    p = 1
    c = c7+c15+c17+c1+c18+c3+c6
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
check HiddenDocument_r0_c10{ HiddenDocument[r0,c10]} for 4
check HiddenDocument_r0_c11{ HiddenDocument[r0,c11]} for 4
check HiddenDocument_r0_c12{ HiddenDocument[r0,c12]} for 4
check HiddenDocument_r0_c13{ HiddenDocument[r0,c13]} for 4
check HiddenDocument_r0_c14{ HiddenDocument[r0,c14]} for 4
check HiddenDocument_r0_c15{ HiddenDocument[r0,c15]} for 4
check HiddenDocument_r0_c16{ HiddenDocument[r0,c16]} for 4
check HiddenDocument_r0_c17{ HiddenDocument[r0,c17]} for 4
check HiddenDocument_r0_c18{ HiddenDocument[r0,c18]} for 4
check HiddenDocument_r0_c19{ HiddenDocument[r0,c19]} for 4
