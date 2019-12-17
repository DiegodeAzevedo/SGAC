module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s4->s0+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s2+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s5+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s5+
         s10->s9+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s8+
         s12->s3+
         s12->s5+
         s12->s8+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s8+
         s13->s9+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s12+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s11+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s10+
         s16->s11+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s15+
         s19->s17+
         s20->s0+
         s20->s7+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s2+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s13+
         s21->s14+
         s21->s16+
         s22->s6+
         s22->s12+
         s22->s14+
         s22->s15+
         s22->s16+
         s22->s18+
         s22->s21+
         s23->s2+
         s23->s3+
         s23->s5+
         s23->s6+
         s23->s10+
         s23->s11+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s22+
         s24->s2+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s19+
         s24->s21+
         s24->s23+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s7+
         s25->s10+
         s25->s13+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s11+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s20+
         s26->s25+
         s27->s0+
         s27->s2+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s9+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s21+
         s27->s22+
         s28->s3+
         s28->s7+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s27+
         s29->s0+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s9+
         s29->s12+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s20+
         s29->s23+
         s29->s25+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r0+
         r3->r1+
         r4->r1+
         r5->r2+
         r5->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r11+
         r13->r3+
         r13->r4+
         r13->r8+
         r13->r11+
         r14->r1+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r2+
         r15->r4+
         r15->r7+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r15+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r7+
         r18->r11+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r13+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r9+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r12+
         r21->r17+
         r22->r1+
         r22->r4+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r11+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r20+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r17+
         r23->r18+
         r23->r20+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r7+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r5+
         r25->r6+
         r25->r9+
         r25->r10+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r23+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r9+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r21+
         r26->r22+
         r26->r24+
         r27->r8+
         r27->r9+
         r27->r12+
         r27->r15+
         r27->r19+
         r27->r21+
         r27->r22+
         r27->r23+
         r28->r1+
         r28->r2+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r11+
         r28->r12+
         r28->r15+
         r28->r17+
         r28->r20+
         r28->r21+
         r28->r23+
         r28->r26+
         r29->r0+
         r29->r1+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r18+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r25+
         r29->r26+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r3
    m = prohibition
    p = 0
    c = c8+c4+c5+c3
}
one sig rule1 extends Rule{}{
    s =s2
    t =r0
    m = prohibition
    p = 3
    c = c0
}
one sig rule2 extends Rule{}{
    s =s17
    t =r17
    m = prohibition
    p = 1
    c = c1+c8+c2+c5+c0
}
one sig rule3 extends Rule{}{
    s =s9
    t =r22
    m = permission
    p = 1
    c = c5+c2+c8+c9+c0
}
one sig rule4 extends Rule{}{
    s =s8
    t =r8
    m = permission
    p = 3
    c = c6+c5+c4
}
one sig rule5 extends Rule{}{
    s =s17
    t =r23
    m = prohibition
    p = 1
    c = c6+c2
}
one sig rule6 extends Rule{}{
    s =s17
    t =r20
    m = permission
    p = 3
    c = c9
}
one sig rule7 extends Rule{}{
    s =s4
    t =r24
    m = prohibition
    p = 3
    c = c6+c1+c8+c0+c9+c4+c2
}
one sig rule8 extends Rule{}{
    s =s0
    t =r2
    m = permission
    p = 2
    c = c5+c2+c3+c9+c0+c7
}
one sig rule9 extends Rule{}{
    s =s13
    t =r25
    m = prohibition
    p = 2
    c = c5+c7+c0
}
one sig rule10 extends Rule{}{
    s =s28
    t =r23
    m = prohibition
    p = 0
    c = c8+c2
}
one sig rule11 extends Rule{}{
    s =s0
    t =r23
    m = permission
    p = 4
    c = c8
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
