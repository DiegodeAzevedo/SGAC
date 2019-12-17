module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s1+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s5+
         s9->s6+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s7+
         s10->s8+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s5+
         s13->s11+
         s14->s0+
         s14->s5+
         s14->s7+
         s14->s9+
         s14->s11+
         s14->s12+
         s15->s1+
         s15->s3+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s13+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s7+
         s16->s10+
         s16->s14+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s4+
         s18->s6+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s14+
         s20->s15+
         s20->s19+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s15+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s8+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s18+
         s22->s19+
         s23->s2+
         s23->s3+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s15+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s22+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s2+
         s26->s3+
         s26->s5+
         s26->s7+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s16+
         s26->s18+
         s26->s19+
         s26->s20+
         s27->s2+
         s27->s5+
         s27->s9+
         s27->s10+
         s27->s15+
         s27->s16+
         s27->s20+
         s27->s23+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s24+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s11+
         s29->s14+
         s29->s17+
         s29->s20+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r2+
         r5->r4+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r1+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r10+
         r15->r14+
         r16->r7+
         r16->r11+
         r16->r13+
         r17->r1+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r14+
         r17->r15+
         r18->r1+
         r18->r5+
         r18->r6+
         r18->r10+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r8+
         r19->r10+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r0+
         r20->r1+
         r20->r3+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r13+
         r20->r15+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r14+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r7+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r19+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r16+
         r24->r19+
         r24->r20+
         r24->r21+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r20+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r13+
         r27->r14+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r5+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r20+
         r28->r21+
         r28->r24+
         r28->r25+
         r28->r27+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r16+
         r29->r18+
         r29->r22+
         r29->r24+
         r29->r27+
         r29->r28}

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
    s =s20
    t =r12
    m = permission
    p = 4
    c = c3+c7+c2+c1+c9+c0+c8
}
one sig rule1 extends Rule{}{
    s =s2
    t =r0
    m = prohibition
    p = 1
    c = c2+c8
}
one sig rule2 extends Rule{}{
    s =s15
    t =r5
    m = prohibition
    p = 0
    c = c0
}
one sig rule3 extends Rule{}{
    s =s6
    t =r23
    m = prohibition
    p = 0
    c = c2
}
one sig rule4 extends Rule{}{
    s =s7
    t =r1
    m = permission
    p = 1
    c = c8
}
one sig rule5 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 3
    c = c3+c1+c7
}
one sig rule6 extends Rule{}{
    s =s15
    t =r17
    m = prohibition
    p = 2
    c = c6+c9+c8+c0+c3+c4
}
one sig rule7 extends Rule{}{
    s =s13
    t =r10
    m = permission
    p = 3
    c = c3+c6+c7+c2
}
one sig rule8 extends Rule{}{
    s =s10
    t =r4
    m = prohibition
    p = 0
    c = c9+c8+c7+c4+c1+c2
}
one sig rule9 extends Rule{}{
    s =s28
    t =r22
    m = prohibition
    p = 1
    c = c7+c0+c4+c8+c5
}
one sig rule10 extends Rule{}{
    s =s20
    t =r17
    m = permission
    p = 3
    c = c0+c3
}
one sig rule11 extends Rule{}{
    s =s29
    t =r16
    m = permission
    p = 3
    c = c7+c2+c8
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
