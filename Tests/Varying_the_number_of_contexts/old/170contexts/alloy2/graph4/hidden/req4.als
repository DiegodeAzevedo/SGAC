module filepath/param/graph/property/req
open filepath/alloy2/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s4->s3+
         s5->s0+
         s5->s3+
         s7->s4+
         s7->s5+
         s8->s1+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s7+
         s10->s8+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s8+
         s12->s0+
         s12->s1+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s1+
         s13->s7+
         s13->s9+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s6+
         s15->s7+
         s15->s9+
         s15->s12+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s11+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s17+
         s19->s2+
         s19->s3+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s17+
         s20->s0+
         s20->s4+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s18+
         s21->s3+
         s21->s4+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s18+
         s22->s0+
         s22->s2+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s1+
         s23->s3+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s11+
         s23->s14+
         s23->s18+
         s23->s20+
         s24->s3+
         s24->s4+
         s24->s6+
         s24->s9+
         s24->s11+
         s24->s14+
         s24->s20+
         s24->s22+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s4+
         s25->s5+
         s25->s7+
         s25->s13+
         s25->s18+
         s25->s19+
         s25->s21+
         s25->s22+
         s26->s0+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s22+
         s26->s23+
         s26->s25+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s8+
         s27->s10+
         s27->s11+
         s27->s13+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s24+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s4+
         s28->s5+
         s28->s9+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s16+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s2+
         s29->s6+
         s29->s9+
         s29->s12+
         s29->s13+
         s29->s14+
         s29->s17+
         s29->s18+
         s29->s23+
         s29->s24+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r3->r0+
         r3->r2+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r4+
         r7->r2+
         r7->r5+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r6+
         r9->r3+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r6+
         r11->r8+
         r11->r9+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r7+
         r13->r0+
         r13->r1+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r9+
         r13->r10+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r2+
         r15->r4+
         r15->r9+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r1+
         r16->r5+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r12+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r3+
         r17->r6+
         r17->r11+
         r18->r1+
         r18->r3+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r16+
         r19->r17+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r7+
         r20->r8+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r19+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r1+
         r22->r4+
         r22->r6+
         r22->r7+
         r22->r9+
         r22->r10+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r18+
         r22->r21+
         r23->r0+
         r23->r3+
         r23->r4+
         r23->r6+
         r23->r8+
         r23->r11+
         r23->r14+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r20+
         r23->r22+
         r24->r0+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r15+
         r24->r18+
         r24->r23+
         r25->r0+
         r25->r3+
         r25->r5+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r14+
         r25->r15+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r23+
         r26->r1+
         r26->r2+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r10+
         r26->r11+
         r26->r13+
         r26->r15+
         r26->r17+
         r26->r21+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r4+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r16+
         r27->r17+
         r27->r21+
         r27->r23+
         r27->r26+
         r28->r0+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r12+
         r28->r15+
         r28->r17+
         r28->r21+
         r28->r24+
         r28->r27+
         r29->r1+
         r29->r5+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r14+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r23+
         r29->r24+
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
sub=s6
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s19
    t =r29
    m = prohibition
    p = 1
    c = c5+c1+c8+c3+c0
}
one sig rule1 extends Rule{}{
    s =s4
    t =r28
    m = prohibition
    p = 4
    c = c5+c0+c2+c4+c3+c9+c8+c1
}
one sig rule2 extends Rule{}{
    s =s11
    t =r1
    m = permission
    p = 1
    c = c4+c5+c0
}
one sig rule3 extends Rule{}{
    s =s21
    t =r19
    m = prohibition
    p = 2
    c = c8+c4+c7
}
one sig rule4 extends Rule{}{
    s =s8
    t =r18
    m = prohibition
    p = 4
    c = c6+c0+c5
}
one sig rule5 extends Rule{}{
    s =s13
    t =r23
    m = prohibition
    p = 0
    c = c7+c5+c2+c1+c9+c0+c8
}
one sig rule6 extends Rule{}{
    s =s20
    t =r23
    m = prohibition
    p = 4
    c = c3
}
one sig rule7 extends Rule{}{
    s =s19
    t =r21
    m = permission
    p = 4
    c = c2+c1+c5
}
one sig rule8 extends Rule{}{
    s =s25
    t =r29
    m = permission
    p = 1
    c = c7+c8+c3
}
one sig rule9 extends Rule{}{
    s =s0
    t =r8
    m = prohibition
    p = 3
    c = c3
}
one sig rule10 extends Rule{}{
    s =s17
    t =r19
    m = prohibition
    p = 3
    c = c5+c3+c2+c9
}
one sig rule11 extends Rule{}{
    s =s25
    t =r6
    m = permission
    p = 4
    c = c6+c1+c2
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
