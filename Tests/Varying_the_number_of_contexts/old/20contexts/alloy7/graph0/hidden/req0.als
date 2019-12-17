module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s3+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s2+
         s6->s4+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s3+
         s9->s5+
         s9->s8+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s4+
         s11->s5+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s10+
         s12->s11+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s8+
         s14->s1+
         s14->s4+
         s14->s6+
         s14->s7+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s7+
         s15->s8+
         s15->s9+
         s16->s0+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s13+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s12+
         s18->s17+
         s19->s0+
         s19->s2+
         s19->s6+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s17+
         s20->s0+
         s20->s1+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s7+
         s20->s8+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s6+
         s21->s8+
         s21->s9+
         s21->s14+
         s21->s16+
         s21->s17+
         s21->s19+
         s22->s1+
         s22->s3+
         s22->s5+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s17+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s6+
         s23->s10+
         s23->s11+
         s23->s14+
         s23->s19+
         s23->s22+
         s24->s0+
         s24->s4+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s11+
         s24->s16+
         s24->s18+
         s24->s20+
         s24->s22+
         s25->s0+
         s25->s3+
         s25->s5+
         s25->s7+
         s25->s8+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s24+
         s26->s1+
         s26->s8+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s7+
         s27->s8+
         s27->s11+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s21+
         s27->s22+
         s28->s2+
         s28->s3+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s12+
         s28->s13+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s27+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s9+
         s29->s11+
         s29->s15+
         s29->s18+
         s29->s19+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r4->r1+
         r5->r1+
         r5->r3+
         r5->r4+
         r7->r0+
         r7->r4+
         r7->r6+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r2+
         r9->r3+
         r10->r2+
         r10->r4+
         r10->r7+
         r11->r4+
         r11->r5+
         r11->r8+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r7+
         r13->r9+
         r13->r12+
         r14->r1+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r7+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r7+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r15+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r3+
         r21->r6+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r20+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r18+
         r22->r19+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r18+
         r24->r20+
         r24->r23+
         r25->r2+
         r25->r9+
         r25->r10+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r22+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r7+
         r26->r9+
         r26->r14+
         r26->r18+
         r26->r20+
         r26->r22+
         r26->r25+
         r27->r0+
         r27->r2+
         r27->r7+
         r27->r8+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r16+
         r27->r17+
         r27->r23+
         r27->r25+
         r27->r26+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r13+
         r28->r14+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r23+
         r28->r25+
         r28->r26+
         r29->r0+
         r29->r1+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r10+
         r29->r16+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r23+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s6
    t =r21
    m = prohibition
    p = 2
    c = c5+c0+c9+c4+c7
}
one sig rule1 extends Rule{}{
    s =s12
    t =r18
    m = prohibition
    p = 2
    c = c9+c4+c6+c2+c0+c8+c5
}
one sig rule2 extends Rule{}{
    s =s10
    t =r5
    m = permission
    p = 4
    c = c0+c3+c9+c1
}
one sig rule3 extends Rule{}{
    s =s29
    t =r21
    m = permission
    p = 4
    c = c1+c8+c7+c3
}
one sig rule4 extends Rule{}{
    s =s26
    t =r15
    m = permission
    p = 2
    c = c3+c5
}
one sig rule5 extends Rule{}{
    s =s4
    t =r0
    m = prohibition
    p = 3
    c = c6+c5+c8+c4+c1+c3
}
one sig rule6 extends Rule{}{
    s =s14
    t =r22
    m = permission
    p = 4
    c = c1+c4
}
one sig rule7 extends Rule{}{
    s =s28
    t =r0
    m = prohibition
    p = 1
    c = c8+c1+c4+c6+c5+c7+c0
}
one sig rule8 extends Rule{}{
    s =s12
    t =r27
    m = permission
    p = 3
    c = c6+c9+c1+c3+c0+c7
}
one sig rule9 extends Rule{}{
    s =s6
    t =r11
    m = prohibition
    p = 4
    c = c4+c0+c6+c3+c9+c1
}
one sig rule10 extends Rule{}{
    s =s8
    t =r10
    m = permission
    p = 3
    c = c5+c4+c8+c1
}
one sig rule11 extends Rule{}{
    s =s14
    t =r22
    m = prohibition
    p = 0
    c = c8+c2+c0+c3
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
