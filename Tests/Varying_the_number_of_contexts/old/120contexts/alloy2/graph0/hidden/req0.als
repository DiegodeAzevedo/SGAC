module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s3+
         s7->s0+
         s7->s1+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s9->s1+
         s10->s0+
         s10->s4+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s7+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s11+
         s14->s13+
         s15->s4+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s11+
         s16->s0+
         s16->s4+
         s16->s5+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s15+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s6+
         s18->s8+
         s18->s9+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s18+
         s20->s2+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s19+
         s21->s0+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s10+
         s21->s13+
         s21->s16+
         s21->s18+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s12+
         s22->s20+
         s22->s21+
         s23->s2+
         s23->s4+
         s23->s7+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s22+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s7+
         s24->s8+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s5+
         s25->s7+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s18+
         s25->s23+
         s26->s2+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s13+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s21+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s12+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s24+
         s27->s25+
         s28->s0+
         s28->s2+
         s28->s3+
         s28->s5+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s17+
         s28->s22+
         s28->s23+
         s28->s25+
         s28->s26+
         s29->s1+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s18+
         s29->s19+
         s29->s21+
         s29->s22+
         s29->s24+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r6->r1+
         r6->r2+
         r6->r5+
         r7->r1+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r7+
         r10->r0+
         r10->r4+
         r10->r5+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r2+
         r12->r7+
         r13->r5+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r5+
         r16->r10+
         r16->r13+
         r16->r14+
         r17->r2+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r11+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r13+
         r19->r16+
         r19->r17+
         r20->r2+
         r20->r5+
         r20->r6+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r3+
         r22->r5+
         r22->r8+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r15+
         r24->r20+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r3+
         r25->r5+
         r25->r6+
         r25->r9+
         r25->r11+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r23+
         r26->r1+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r23+
         r26->r25+
         r27->r2+
         r27->r3+
         r27->r6+
         r27->r9+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r17+
         r27->r19+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r10+
         r28->r13+
         r28->r14+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r22+
         r28->r24+
         r28->r25+
         r29->r5+
         r29->r8+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22}

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
    s =s13
    t =r15
    m = prohibition
    p = 3
    c = c6+c0+c8+c5+c2+c3
}
one sig rule1 extends Rule{}{
    s =s22
    t =r8
    m = permission
    p = 1
    c = c8+c0+c1+c2+c3
}
one sig rule2 extends Rule{}{
    s =s18
    t =r28
    m = prohibition
    p = 0
    c = c3+c5+c1+c0+c2
}
one sig rule3 extends Rule{}{
    s =s29
    t =r17
    m = permission
    p = 3
    c = c3+c4+c9+c6+c1+c7
}
one sig rule4 extends Rule{}{
    s =s14
    t =r23
    m = prohibition
    p = 3
    c = c9+c5
}
one sig rule5 extends Rule{}{
    s =s13
    t =r23
    m = prohibition
    p = 0
    c = c9+c8+c1
}
one sig rule6 extends Rule{}{
    s =s3
    t =r20
    m = prohibition
    p = 0
    c = c5+c9
}
one sig rule7 extends Rule{}{
    s =s15
    t =r11
    m = permission
    p = 2
    c = c9
}
one sig rule8 extends Rule{}{
    s =s26
    t =r3
    m = prohibition
    p = 4
    c = c9+c5+c2+c6+c1+c0
}
one sig rule9 extends Rule{}{
    s =s29
    t =r10
    m = permission
    p = 2
    c = c4+c2+c5+c1
}
one sig rule10 extends Rule{}{
    s =s13
    t =r11
    m = prohibition
    p = 0
    c = c3+c0+c1
}
one sig rule11 extends Rule{}{
    s =s22
    t =r12
    m = permission
    p = 3
    c = c5+c4+c1+c8
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
