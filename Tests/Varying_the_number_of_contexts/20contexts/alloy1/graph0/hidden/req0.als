module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s4->s1+
         s5->s1+
         s5->s2+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s0+
         s7->s1+
         s7->s2+
         s8->s4+
         s8->s5+
         s8->s6+
         s9->s2+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s14+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s9+
         s16->s10+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s15+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s7+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s18+
         s20->s1+
         s20->s3+
         s20->s6+
         s20->s9+
         s20->s10+
         s20->s12+
         s20->s15+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s3+
         s21->s6+
         s21->s8+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s5+
         s22->s7+
         s22->s10+
         s22->s13+
         s22->s15+
         s22->s16+
         s23->s2+
         s23->s6+
         s23->s8+
         s23->s10+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s14+
         s24->s15+
         s24->s17+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s3+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s13+
         s25->s14+
         s25->s17+
         s25->s18+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s13+
         s26->s19+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s20+
         s27->s21+
         s27->s23+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s23+
         s29->s1+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s11+
         s29->s13+
         s29->s16+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r3->r0+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r2+
         r5->r3+
         r6->r0+
         r7->r0+
         r7->r1+
         r7->r4+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r6+
         r11->r1+
         r11->r4+
         r11->r6+
         r11->r7+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r3+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r14+
         r17->r0+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r14+
         r18->r0+
         r18->r1+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r8+
         r19->r12+
         r19->r14+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r19+
         r21->r4+
         r21->r5+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r8+
         r22->r11+
         r22->r13+
         r22->r15+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r0+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r13+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r2+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r13+
         r24->r14+
         r24->r17+
         r24->r19+
         r24->r20+
         r25->r0+
         r25->r2+
         r25->r4+
         r25->r9+
         r25->r10+
         r25->r15+
         r25->r16+
         r25->r19+
         r25->r21+
         r25->r24+
         r26->r4+
         r26->r6+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r27->r1+
         r27->r2+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r12+
         r27->r13+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r23+
         r28->r0+
         r28->r2+
         r28->r6+
         r28->r10+
         r28->r14+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r2+
         r29->r5+
         r29->r7+
         r29->r8+
         r29->r9+
         r29->r15+
         r29->r17+
         r29->r19+
         r29->r22+
         r29->r23+
         r29->r25}

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
    s =s29
    t =r6
    m = prohibition
    p = 2
    c = c19+c9
}
one sig rule1 extends Rule{}{
    s =s19
    t =r1
    m = prohibition
    p = 2
    c = c8+c7+c11+c6+c3+c12+c15+c5+c2+c10+c9+c1
}
one sig rule2 extends Rule{}{
    s =s9
    t =r25
    m = prohibition
    p = 0
    c = c12+c9+c16+c4+c13+c19+c1+c5+c2+c18+c6+c0+c11+c7
}
one sig rule3 extends Rule{}{
    s =s20
    t =r29
    m = prohibition
    p = 2
    c = c15+c13+c16+c10+c1+c14+c17+c12+c19+c5+c6+c2+c11
}
one sig rule4 extends Rule{}{
    s =s26
    t =r10
    m = prohibition
    p = 1
    c = c3+c2+c11+c15+c7+c17+c8
}
one sig rule5 extends Rule{}{
    s =s29
    t =r12
    m = prohibition
    p = 0
    c = c16+c7+c2+c0+c5+c11+c19+c10+c15+c4+c12+c1
}
one sig rule6 extends Rule{}{
    s =s25
    t =r25
    m = prohibition
    p = 4
    c = c12+c1+c8
}
one sig rule7 extends Rule{}{
    s =s22
    t =r25
    m = permission
    p = 4
    c = c6+c4+c15+c0+c19+c8+c11+c18+c7+c5+c2+c3+c12
}
one sig rule8 extends Rule{}{
    s =s6
    t =r5
    m = permission
    p = 1
    c = c11+c8+c5+c18+c19+c7+c12+c0+c4
}
one sig rule9 extends Rule{}{
    s =s25
    t =r4
    m = permission
    p = 3
    c = c14+c10+c4
}
one sig rule10 extends Rule{}{
    s =s5
    t =r26
    m = permission
    p = 2
    c = c12+c6+c8+c0+c3+c1+c13+c14+c2+c11
}
one sig rule11 extends Rule{}{
    s =s29
    t =r12
    m = permission
    p = 3
    c = c6+c17+c11
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
