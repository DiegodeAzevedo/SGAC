module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s3->s2+
         s4->s1+
         s4->s2+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s3+
         s9->s0+
         s9->s2+
         s9->s3+
         s9->s5+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s7+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s8+
         s12->s10+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s12+
         s14->s0+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s8+
         s16->s11+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s4+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s7+
         s18->s8+
         s18->s12+
         s18->s16+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s17+
         s19->s18+
         s20->s1+
         s20->s4+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s14+
         s21->s17+
         s22->s0+
         s22->s2+
         s22->s6+
         s22->s7+
         s22->s10+
         s22->s13+
         s22->s14+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s12+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s9+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s10+
         s25->s13+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s22+
         s25->s23+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s23+
         s27->s8+
         s27->s12+
         s27->s15+
         s27->s16+
         s27->s18+
         s27->s19+
         s27->s22+
         s27->s23+
         s27->s24+
         s27->s25+
         s28->s1+
         s28->s4+
         s28->s6+
         s28->s7+
         s28->s15+
         s28->s18+
         s28->s20+
         s28->s23+
         s28->s24+
         s28->s27+
         s29->s2+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s17+
         s29->s21+
         s29->s22+
         s29->s25+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r2+
         r5->r4+
         r6->r5+
         r7->r0+
         r7->r6+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r6+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r6+
         r11->r9+
         r12->r1+
         r12->r7+
         r12->r8+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r10+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r7+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r3+
         r15->r4+
         r15->r6+
         r15->r8+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r3+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r12+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r11+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r8+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r18+
         r20->r0+
         r20->r2+
         r20->r5+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r12+
         r20->r14+
         r20->r17+
         r20->r19+
         r21->r2+
         r21->r4+
         r21->r5+
         r21->r8+
         r21->r9+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r15+
         r22->r17+
         r22->r18+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r22+
         r24->r1+
         r24->r3+
         r24->r6+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r15+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r7+
         r26->r9+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r16+
         r26->r22+
         r26->r24+
         r27->r0+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r12+
         r27->r16+
         r27->r18+
         r27->r19+
         r27->r21+
         r27->r22+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r4+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r23+
         r28->r24+
         r28->r25+
         r28->r26+
         r28->r27+
         r29->r0+
         r29->r2+
         r29->r3+
         r29->r8+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r24+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

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
    s =s5
    t =r28
    m = prohibition
    p = 4
    c = c5+c6+c0
}
one sig rule1 extends Rule{}{
    s =s16
    t =r29
    m = prohibition
    p = 2
    c = c4+c9+c2+c3+c8
}
one sig rule2 extends Rule{}{
    s =s1
    t =r4
    m = permission
    p = 3
    c = c6+c7+c4+c0+c8
}
one sig rule3 extends Rule{}{
    s =s11
    t =r25
    m = prohibition
    p = 0
    c = c1+c9+c6
}
one sig rule4 extends Rule{}{
    s =s22
    t =r13
    m = permission
    p = 2
    c = c7+c3+c6+c4
}
one sig rule5 extends Rule{}{
    s =s25
    t =r10
    m = prohibition
    p = 4
    c = c2
}
one sig rule6 extends Rule{}{
    s =s3
    t =r1
    m = prohibition
    p = 4
    c = c2+c7+c1+c9
}
one sig rule7 extends Rule{}{
    s =s17
    t =r27
    m = prohibition
    p = 1
    c = c5+c1
}
one sig rule8 extends Rule{}{
    s =s23
    t =r26
    m = prohibition
    p = 1
    c = c7+c0+c9
}
one sig rule9 extends Rule{}{
    s =s15
    t =r14
    m = permission
    p = 1
    c = c1
}
one sig rule10 extends Rule{}{
    s =s4
    t =r14
    m = prohibition
    p = 4
    c = c2+c0+c4+c7
}
one sig rule11 extends Rule{}{
    s =s12
    t =r27
    m = permission
    p = 0
    c = c8+c0+c3+c7+c2+c5
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
