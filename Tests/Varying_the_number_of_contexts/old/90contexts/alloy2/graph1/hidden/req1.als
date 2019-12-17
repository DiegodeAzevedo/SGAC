module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s2+
         s4->s1+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s3+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s1+
         s9->s1+
         s9->s6+
         s9->s8+
         s10->s2+
         s10->s3+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s8+
         s11->s9+
         s12->s2+
         s12->s3+
         s12->s4+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s3+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s14->s0+
         s14->s1+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s14+
         s18->s0+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s1+
         s20->s4+
         s20->s5+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s19+
         s21->s0+
         s21->s4+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s13+
         s21->s14+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s11+
         s22->s15+
         s22->s19+
         s23->s0+
         s23->s2+
         s23->s4+
         s23->s6+
         s23->s8+
         s23->s10+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s2+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s13+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s20+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s3+
         s25->s5+
         s25->s10+
         s25->s11+
         s25->s13+
         s25->s16+
         s25->s19+
         s25->s24+
         s26->s2+
         s26->s3+
         s26->s8+
         s26->s10+
         s26->s12+
         s26->s15+
         s26->s17+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s13+
         s27->s14+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s22+
         s27->s24+
         s27->s26+
         s28->s3+
         s28->s5+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s17+
         s28->s20+
         s28->s21+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s4+
         s29->s7+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s22+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r4->r2+
         r4->r3+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r0+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r5+
         r8->r7+
         r9->r2+
         r9->r7+
         r10->r0+
         r10->r4+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r3+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r12+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r15->r1+
         r15->r2+
         r15->r6+
         r15->r7+
         r15->r14+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r11+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r15+
         r19->r1+
         r19->r4+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r14+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r14+
         r21->r16+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r21+
         r23->r0+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r11+
         r23->r12+
         r23->r13+
         r23->r16+
         r23->r17+
         r23->r19+
         r23->r20+
         r24->r0+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r11+
         r25->r13+
         r25->r14+
         r25->r16+
         r25->r17+
         r25->r21+
         r25->r22+
         r26->r0+
         r26->r2+
         r26->r4+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r22+
         r27->r1+
         r27->r5+
         r27->r9+
         r27->r10+
         r27->r12+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r22+
         r27->r24+
         r28->r2+
         r28->r4+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r14+
         r28->r15+
         r28->r20+
         r28->r22+
         r28->r23+
         r28->r25+
         r29->r0+
         r29->r5+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r25}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req1 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r16
    m = prohibition
    p = 1
    c = c9+c1+c5
}
one sig rule1 extends Rule{}{
    s =s15
    t =r10
    m = permission
    p = 0
    c = c0+c3+c5+c9+c7+c6
}
one sig rule2 extends Rule{}{
    s =s10
    t =r2
    m = permission
    p = 2
    c = c7+c6+c5+c4+c9+c2
}
one sig rule3 extends Rule{}{
    s =s20
    t =r15
    m = prohibition
    p = 1
    c = c5+c2+c3
}
one sig rule4 extends Rule{}{
    s =s2
    t =r19
    m = prohibition
    p = 3
    c = c9+c6+c1
}
one sig rule5 extends Rule{}{
    s =s1
    t =r0
    m = prohibition
    p = 1
    c = c3+c9
}
one sig rule6 extends Rule{}{
    s =s13
    t =r8
    m = prohibition
    p = 2
    c = c7+c2+c1+c5
}
one sig rule7 extends Rule{}{
    s =s24
    t =r25
    m = prohibition
    p = 3
    c = c2
}
one sig rule8 extends Rule{}{
    s =s9
    t =r26
    m = permission
    p = 4
    c = c9+c3+c6+c0+c1+c7
}
one sig rule9 extends Rule{}{
    s =s7
    t =r26
    m = permission
    p = 0
    c = c8
}
one sig rule10 extends Rule{}{
    s =s22
    t =r0
    m = prohibition
    p = 2
    c = c9+c6+c2+c5+c0+c8
}
one sig rule11 extends Rule{}{
    s =s28
    t =r16
    m = prohibition
    p = 0
    c = c9+c2+c6+c5+c3+c1
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
check HiddenDocument_r2_c0{ HiddenDocument[r2,c0]} for 4
check HiddenDocument_r2_c1{ HiddenDocument[r2,c1]} for 4
check HiddenDocument_r2_c2{ HiddenDocument[r2,c2]} for 4
check HiddenDocument_r2_c3{ HiddenDocument[r2,c3]} for 4
check HiddenDocument_r2_c4{ HiddenDocument[r2,c4]} for 4
check HiddenDocument_r2_c5{ HiddenDocument[r2,c5]} for 4
check HiddenDocument_r2_c6{ HiddenDocument[r2,c6]} for 4
check HiddenDocument_r2_c7{ HiddenDocument[r2,c7]} for 4
check HiddenDocument_r2_c8{ HiddenDocument[r2,c8]} for 4
check HiddenDocument_r2_c9{ HiddenDocument[r2,c9]} for 4
