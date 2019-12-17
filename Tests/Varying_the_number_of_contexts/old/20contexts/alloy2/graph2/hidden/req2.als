module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s3+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s4+
         s11->s5+
         s11->s7+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s6+
         s13->s7+
         s13->s10+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s10+
         s14->s12+
         s15->s2+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s11+
         s16->s0+
         s16->s2+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s14+
         s17->s2+
         s17->s3+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s6+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s4+
         s20->s8+
         s20->s15+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s2+
         s21->s4+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s16+
         s21->s18+
         s21->s19+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s9+
         s22->s12+
         s22->s13+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s3+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s17+
         s24->s18+
         s24->s20+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s9+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s21+
         s25->s24+
         s26->s1+
         s26->s4+
         s26->s6+
         s26->s9+
         s26->s12+
         s26->s16+
         s26->s20+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s4+
         s27->s7+
         s27->s9+
         s27->s13+
         s27->s16+
         s27->s18+
         s27->s20+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s5+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s21+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s8+
         s29->s12+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s22+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r2+
         r6->r0+
         r6->r1+
         r6->r3+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r7+
         r9->r5+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r4+
         r11->r5+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r3+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r8+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r16+
         r19->r17+
         r20->r2+
         r20->r6+
         r20->r11+
         r20->r12+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r8+
         r21->r11+
         r21->r12+
         r21->r15+
         r21->r16+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r6+
         r22->r7+
         r22->r9+
         r22->r14+
         r22->r21+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r4+
         r23->r6+
         r23->r8+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r19+
         r23->r21+
         r24->r1+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r11+
         r24->r16+
         r24->r21+
         r24->r23+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r17+
         r25->r18+
         r25->r22+
         r25->r23+
         r26->r2+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r12+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r20+
         r26->r24+
         r26->r25+
         r27->r3+
         r27->r4+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r19+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r0+
         r28->r2+
         r28->r5+
         r28->r7+
         r28->r9+
         r28->r13+
         r28->r14+
         r28->r16+
         r28->r18+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r26+
         r29->r0+
         r29->r5+
         r29->r9+
         r29->r14+
         r29->r17+
         r29->r18+
         r29->r22+
         r29->r23+
         r29->r25+
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
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s13
    t =r16
    m = prohibition
    p = 3
    c = c5+c4+c9+c2+c0
}
one sig rule1 extends Rule{}{
    s =s4
    t =r9
    m = prohibition
    p = 0
    c = c7+c8
}
one sig rule2 extends Rule{}{
    s =s12
    t =r10
    m = permission
    p = 1
    c = c5
}
one sig rule3 extends Rule{}{
    s =s17
    t =r11
    m = prohibition
    p = 0
    c = c0+c6+c2+c3
}
one sig rule4 extends Rule{}{
    s =s6
    t =r23
    m = permission
    p = 4
    c = c8+c1+c4+c2+c3+c7
}
one sig rule5 extends Rule{}{
    s =s16
    t =r14
    m = prohibition
    p = 0
    c = c6+c4+c9+c5
}
one sig rule6 extends Rule{}{
    s =s11
    t =r10
    m = permission
    p = 0
    c = c6+c8+c3+c0+c7+c1
}
one sig rule7 extends Rule{}{
    s =s13
    t =r26
    m = permission
    p = 3
    c = c9+c6+c7+c5+c8+c0+c1
}
one sig rule8 extends Rule{}{
    s =s28
    t =r13
    m = permission
    p = 1
    c = c3+c4+c5+c6+c7
}
one sig rule9 extends Rule{}{
    s =s12
    t =r12
    m = prohibition
    p = 0
    c = c7+c2+c3
}
one sig rule10 extends Rule{}{
    s =s17
    t =r11
    m = prohibition
    p = 1
    c = c4+c7
}
one sig rule11 extends Rule{}{
    s =s24
    t =r13
    m = permission
    p = 1
    c = c6
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
