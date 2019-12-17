module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s2+
         s4->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s0+
         s8->s3+
         s8->s6+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s7+
         s9->s8+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s4+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s8+
         s14->s13+
         s15->s0+
         s15->s4+
         s15->s6+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s3+
         s16->s4+
         s16->s6+
         s16->s8+
         s16->s11+
         s16->s12+
         s16->s14+
         s17->s1+
         s17->s3+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s9+
         s18->s11+
         s19->s0+
         s19->s1+
         s19->s8+
         s19->s12+
         s19->s18+
         s20->s3+
         s20->s5+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s17+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s6+
         s22->s7+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s16+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s3+
         s23->s5+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s21+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s2+
         s25->s5+
         s25->s6+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s19+
         s25->s20+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s4+
         s27->s6+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s23+
         s27->s24+
         s27->s25+
         s28->s1+
         s28->s2+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s12+
         s28->s15+
         s28->s16+
         s28->s19+
         s28->s21+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s3+
         s29->s6+
         s29->s9+
         s29->s10+
         s29->s12+
         s29->s16+
         s29->s18+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s24+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r4->r1+
         r4->r3+
         r5->r4+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r5+
         r8->r1+
         r8->r4+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r6+
         r9->r8+
         r10->r6+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r5+
         r12->r8+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r8+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r7+
         r14->r10+
         r14->r11+
         r15->r0+
         r15->r1+
         r15->r4+
         r15->r9+
         r15->r10+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r9+
         r18->r11+
         r18->r13+
         r18->r14+
         r18->r16+
         r18->r17+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r20->r1+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r15+
         r20->r18+
         r21->r1+
         r21->r2+
         r21->r4+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r15+
         r21->r17+
         r22->r0+
         r22->r2+
         r22->r6+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r9+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r18+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r5+
         r24->r7+
         r24->r8+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r16+
         r24->r18+
         r24->r20+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r8+
         r25->r15+
         r25->r17+
         r26->r2+
         r26->r4+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r18+
         r26->r20+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r10+
         r27->r14+
         r27->r17+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r25+
         r28->r0+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r8+
         r28->r14+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r22+
         r28->r23+
         r28->r26+
         r29->r11+
         r29->r13+
         r29->r15+
         r29->r17+
         r29->r18+
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
res=r2
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r5
    m = permission
    p = 3
    c = c8+c6+c0+c3+c7+c4
}
one sig rule1 extends Rule{}{
    s =s16
    t =r14
    m = prohibition
    p = 4
    c = c6+c9+c1+c4+c0+c5
}
one sig rule2 extends Rule{}{
    s =s25
    t =r25
    m = prohibition
    p = 2
    c = c6+c7+c8+c1
}
one sig rule3 extends Rule{}{
    s =s21
    t =r12
    m = permission
    p = 0
    c = c4+c9+c7+c8+c6+c1
}
one sig rule4 extends Rule{}{
    s =s12
    t =r13
    m = prohibition
    p = 4
    c = c5+c7
}
one sig rule5 extends Rule{}{
    s =s6
    t =r23
    m = permission
    p = 2
    c = c4
}
one sig rule6 extends Rule{}{
    s =s11
    t =r18
    m = permission
    p = 0
    c = c9+c5+c8
}
one sig rule7 extends Rule{}{
    s =s16
    t =r1
    m = permission
    p = 4
    c = c2+c7
}
one sig rule8 extends Rule{}{
    s =s26
    t =r7
    m = permission
    p = 4
    c = c7+c9+c2+c3+c4+c0+c1
}
one sig rule9 extends Rule{}{
    s =s11
    t =r13
    m = permission
    p = 1
    c = c1+c2+c3+c0+c6+c4
}
one sig rule10 extends Rule{}{
    s =s19
    t =r0
    m = permission
    p = 1
    c = c4+c0+c5+c6+c7+c3+c1
}
one sig rule11 extends Rule{}{
    s =s11
    t =r13
    m = permission
    p = 2
    c = c9+c6+c1+c3
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
