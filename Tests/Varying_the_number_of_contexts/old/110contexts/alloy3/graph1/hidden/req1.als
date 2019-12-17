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
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s4+
         s7->s1+
         s7->s3+
         s7->s4+
         s8->s1+
         s8->s2+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s5+
         s9->s8+
         s10->s0+
         s10->s4+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s9+
         s15->s1+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s11+
         s15->s14+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s11+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s10+
         s18->s11+
         s18->s13+
         s19->s0+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s1+
         s20->s2+
         s20->s5+
         s20->s9+
         s20->s12+
         s20->s15+
         s20->s19+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s7+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s16+
         s21->s17+
         s21->s18+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s9+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s5+
         s23->s7+
         s23->s8+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s24->s3+
         s24->s4+
         s24->s6+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s17+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s11+
         s25->s13+
         s25->s14+
         s25->s17+
         s25->s21+
         s25->s24+
         s26->s3+
         s26->s4+
         s26->s10+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s11+
         s27->s18+
         s27->s20+
         s27->s23+
         s27->s24+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s21+
         s28->s23+
         s28->s26+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s22+
         s29->s23+
         s29->s25+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r2+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r8+
         r10->r3+
         r10->r5+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r7+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r3+
         r13->r4+
         r13->r9+
         r13->r10+
         r14->r6+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r11+
         r15->r0+
         r15->r6+
         r15->r10+
         r16->r4+
         r16->r11+
         r16->r12+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r14+
         r17->r15+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r12+
         r18->r14+
         r19->r2+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r15+
         r19->r17+
         r19->r18+
         r20->r2+
         r20->r3+
         r20->r7+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r14+
         r20->r15+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r11+
         r21->r15+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r2+
         r22->r5+
         r22->r6+
         r22->r9+
         r22->r12+
         r22->r13+
         r22->r16+
         r22->r18+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r6+
         r23->r10+
         r23->r11+
         r23->r16+
         r23->r21+
         r23->r22+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r20+
         r24->r21+
         r25->r0+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r24+
         r26->r0+
         r26->r2+
         r26->r3+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r23+
         r26->r25+
         r27->r1+
         r27->r4+
         r27->r9+
         r27->r15+
         r27->r16+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r24+
         r27->r25+
         r28->r1+
         r28->r2+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r12+
         r28->r13+
         r28->r15+
         r28->r17+
         r28->r20+
         r28->r21+
         r28->r23+
         r28->r24+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r17+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r24+
         r29->r25+
         r29->r26}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r8
    m = permission
    p = 4
    c = c1+c9+c0+c4
}
one sig rule1 extends Rule{}{
    s =s26
    t =r10
    m = permission
    p = 1
    c = c0+c5+c2+c9
}
one sig rule2 extends Rule{}{
    s =s17
    t =r16
    m = permission
    p = 2
    c = c4
}
one sig rule3 extends Rule{}{
    s =s8
    t =r6
    m = permission
    p = 2
    c = c8+c1+c6+c0+c2
}
one sig rule4 extends Rule{}{
    s =s9
    t =r10
    m = prohibition
    p = 4
    c = c9+c4+c6+c0+c7+c1+c8
}
one sig rule5 extends Rule{}{
    s =s27
    t =r19
    m = permission
    p = 3
    c = c6+c0+c5+c4+c7
}
one sig rule6 extends Rule{}{
    s =s29
    t =r23
    m = permission
    p = 2
    c = c4+c8+c0
}
one sig rule7 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 0
    c = c7+c2+c9+c3+c6+c5
}
one sig rule8 extends Rule{}{
    s =s22
    t =r23
    m = prohibition
    p = 4
    c = c5+c4+c2+c0+c3
}
one sig rule9 extends Rule{}{
    s =s4
    t =r19
    m = prohibition
    p = 2
    c = c1+c4+c8
}
one sig rule10 extends Rule{}{
    s =s15
    t =r17
    m = permission
    p = 4
    c = c8+c5+c2+c4+c1+c0
}
one sig rule11 extends Rule{}{
    s =s28
    t =r2
    m = prohibition
    p = 1
    c = c9+c7
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
