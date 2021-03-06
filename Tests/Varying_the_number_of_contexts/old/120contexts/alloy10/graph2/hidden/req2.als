module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s2+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s0+
         s9->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s5+
         s15->s8+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s20->s3+
         s20->s5+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s17+
         s21->s0+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s10+
         s21->s15+
         s21->s16+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s11+
         s22->s14+
         s22->s18+
         s22->s19+
         s23->s1+
         s23->s3+
         s23->s5+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s13+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s4+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s16+
         s24->s17+
         s24->s21+
         s25->s1+
         s25->s3+
         s25->s4+
         s25->s7+
         s25->s9+
         s25->s10+
         s25->s11+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s26->s0+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s13+
         s26->s20+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s4+
         s27->s7+
         s27->s9+
         s27->s19+
         s27->s20+
         s27->s23+
         s27->s25+
         s28->s0+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s10+
         s28->s14+
         s28->s16+
         s28->s18+
         s28->s21+
         s28->s22+
         s28->s24+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s3+
         s29->s4+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s19+
         s29->s22+
         s29->s24+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r1+
         r4->r1+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r3+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r1+
         r11->r3+
         r11->r5+
         r11->r10+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r1+
         r13->r6+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r3+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r2+
         r17->r4+
         r17->r7+
         r17->r8+
         r17->r10+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r11+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r9+
         r19->r13+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r11+
         r20->r13+
         r20->r15+
         r20->r16+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r10+
         r21->r12+
         r21->r15+
         r21->r20+
         r22->r5+
         r22->r6+
         r22->r13+
         r22->r14+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r7+
         r23->r10+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r15+
         r24->r17+
         r24->r18+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r6+
         r25->r9+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r17+
         r25->r21+
         r26->r0+
         r26->r2+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r12+
         r26->r15+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r5+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r13+
         r27->r14+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r22+
         r27->r25+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r22+
         r28->r25+
         r28->r26+
         r29->r0+
         r29->r1+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r26+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s3
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s26
    t =r21
    m = permission
    p = 2
    c = c6+c2+c0
}
one sig rule1 extends Rule{}{
    s =s2
    t =r1
    m = prohibition
    p = 1
    c = c3+c6+c9+c4+c0+c2
}
one sig rule2 extends Rule{}{
    s =s6
    t =r28
    m = permission
    p = 4
    c = c8+c5+c9+c0
}
one sig rule3 extends Rule{}{
    s =s19
    t =r11
    m = permission
    p = 1
    c = c6+c4+c9+c8+c3
}
one sig rule4 extends Rule{}{
    s =s1
    t =r16
    m = prohibition
    p = 4
    c = c1+c5+c2+c6+c9+c7
}
one sig rule5 extends Rule{}{
    s =s27
    t =r11
    m = permission
    p = 3
    c = c3+c8+c7
}
one sig rule6 extends Rule{}{
    s =s18
    t =r11
    m = permission
    p = 2
    c = c7+c1+c9+c5+c0+c2
}
one sig rule7 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 0
    c = c9+c1+c8+c4
}
one sig rule8 extends Rule{}{
    s =s9
    t =r12
    m = prohibition
    p = 3
    c = c1+c7
}
one sig rule9 extends Rule{}{
    s =s27
    t =r29
    m = permission
    p = 4
    c = c0
}
one sig rule10 extends Rule{}{
    s =s12
    t =r14
    m = prohibition
    p = 1
    c = c6+c9+c7+c8+c3+c1
}
one sig rule11 extends Rule{}{
    s =s9
    t =r8
    m = prohibition
    p = 2
    c = c7+c6+c9+c5+c1+c2+c3
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
