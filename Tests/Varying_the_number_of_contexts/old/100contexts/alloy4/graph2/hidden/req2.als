module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s4->s1+
         s4->s2+
         s5->s2+
         s5->s4+
         s6->s1+
         s7->s0+
         s7->s2+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s5+
         s9->s0+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s9+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s8+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s3+
         s14->s6+
         s14->s11+
         s14->s12+
         s15->s1+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s9+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s6+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s4+
         s19->s7+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s15+
         s20->s1+
         s20->s3+
         s20->s5+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s13+
         s21->s15+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s1+
         s22->s3+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s14+
         s22->s16+
         s22->s21+
         s23->s1+
         s23->s4+
         s23->s5+
         s23->s9+
         s23->s10+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s19+
         s23->s20+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s17+
         s24->s19+
         s24->s20+
         s25->s0+
         s25->s2+
         s25->s3+
         s25->s7+
         s25->s9+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s17+
         s25->s20+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s10+
         s26->s14+
         s26->s17+
         s26->s19+
         s26->s21+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s1+
         s27->s3+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s21+
         s27->s22+
         s27->s24+
         s28->s1+
         s28->s2+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s13+
         s28->s16+
         s28->s18+
         s28->s20+
         s28->s22+
         s28->s26+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s11+
         s29->s13+
         s29->s15+
         s29->s16+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r2+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r4+
         r7->r0+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r5+
         r10->r5+
         r10->r6+
         r11->r0+
         r11->r3+
         r11->r4+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r8+
         r12->r9+
         r12->r11+
         r13->r1+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r10+
         r14->r1+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r6+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r15+
         r17->r16+
         r18->r1+
         r18->r3+
         r18->r7+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r16+
         r19->r18+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r14+
         r20->r16+
         r21->r0+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r12+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r15+
         r22->r18+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r13+
         r23->r17+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r13+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r22+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r26->r0+
         r26->r1+
         r26->r4+
         r26->r5+
         r26->r9+
         r26->r14+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r22+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r1+
         r27->r2+
         r27->r5+
         r27->r7+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r14+
         r27->r16+
         r27->r19+
         r27->r20+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r8+
         r28->r9+
         r28->r14+
         r28->r19+
         r28->r23+
         r28->r24+
         r28->r25+
         r29->r2+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r9+
         r29->r12+
         r29->r14+
         r29->r21+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r26}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s0
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s10
    t =r13
    m = permission
    p = 3
    c = c7+c5+c8+c2+c1+c4
}
one sig rule1 extends Rule{}{
    s =s28
    t =r6
    m = prohibition
    p = 2
    c = c0+c2+c4+c6+c7+c8
}
one sig rule2 extends Rule{}{
    s =s29
    t =r6
    m = permission
    p = 0
    c = c1+c3+c0+c5+c8+c7
}
one sig rule3 extends Rule{}{
    s =s26
    t =r20
    m = permission
    p = 2
    c = c4+c0+c2
}
one sig rule4 extends Rule{}{
    s =s11
    t =r24
    m = permission
    p = 4
    c = c1+c0+c6+c9
}
one sig rule5 extends Rule{}{
    s =s0
    t =r21
    m = prohibition
    p = 4
    c = c0+c4+c8+c6+c5+c9
}
one sig rule6 extends Rule{}{
    s =s29
    t =r16
    m = prohibition
    p = 2
    c = c0
}
one sig rule7 extends Rule{}{
    s =s24
    t =r8
    m = prohibition
    p = 2
    c = c4+c9+c3+c0
}
one sig rule8 extends Rule{}{
    s =s13
    t =r25
    m = prohibition
    p = 4
    c = c2+c1+c4+c8+c5
}
one sig rule9 extends Rule{}{
    s =s5
    t =r18
    m = prohibition
    p = 3
    c = c4+c7+c2+c9+c8+c3+c6
}
one sig rule10 extends Rule{}{
    s =s4
    t =r16
    m = prohibition
    p = 2
    c = c8
}
one sig rule11 extends Rule{}{
    s =s22
    t =r10
    m = prohibition
    p = 2
    c = c2+c6+c5
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
