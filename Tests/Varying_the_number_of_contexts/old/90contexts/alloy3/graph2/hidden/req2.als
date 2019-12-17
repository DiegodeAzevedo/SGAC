module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s2+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s3+
         s9->s1+
         s9->s6+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s11+
         s13->s12+
         s14->s0+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s11+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s8+
         s15->s10+
         s16->s0+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s8+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s8+
         s17->s9+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s6+
         s18->s8+
         s18->s11+
         s18->s12+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s3+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s18+
         s20->s2+
         s20->s4+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s17+
         s20->s18+
         s20->s19+
         s21->s0+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s10+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s6+
         s22->s7+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s18+
         s22->s21+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s18+
         s23->s20+
         s24->s0+
         s24->s2+
         s24->s5+
         s24->s6+
         s24->s8+
         s24->s12+
         s24->s13+
         s24->s14+
         s24->s16+
         s24->s17+
         s24->s19+
         s25->s0+
         s25->s1+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s8+
         s25->s19+
         s25->s20+
         s25->s22+
         s26->s2+
         s26->s3+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s12+
         s26->s16+
         s26->s17+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s5+
         s27->s8+
         s27->s10+
         s27->s14+
         s27->s17+
         s27->s24+
         s28->s2+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s13+
         s28->s17+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s13+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s24+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r6+
         r8->r7+
         r9->r2+
         r9->r3+
         r10->r0+
         r10->r3+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r8+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r7+
         r12->r9+
         r12->r10+
         r13->r0+
         r13->r4+
         r13->r6+
         r13->r9+
         r14->r1+
         r14->r2+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r11+
         r15->r12+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r14+
         r18->r17+
         r19->r1+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r16+
         r20->r4+
         r20->r5+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r17+
         r20->r19+
         r21->r3+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r14+
         r21->r15+
         r21->r17+
         r21->r18+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r11+
         r22->r14+
         r22->r15+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r2+
         r23->r6+
         r23->r8+
         r23->r11+
         r23->r17+
         r23->r18+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r4+
         r24->r9+
         r24->r10+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r19+
         r24->r20+
         r24->r22+
         r25->r0+
         r25->r2+
         r25->r3+
         r25->r7+
         r25->r13+
         r25->r16+
         r25->r21+
         r25->r23+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r14+
         r26->r19+
         r26->r20+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r5+
         r27->r6+
         r27->r8+
         r27->r11+
         r27->r12+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r23+
         r27->r24+
         r27->r25+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r10+
         r28->r11+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r21+
         r28->r24+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r18+
         r29->r19+
         r29->r25+
         r29->r26}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s1
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s3
    t =r8
    m = prohibition
    p = 0
    c = c0
}
one sig rule1 extends Rule{}{
    s =s19
    t =r11
    m = permission
    p = 3
    c = c2+c9+c0+c4
}
one sig rule2 extends Rule{}{
    s =s5
    t =r22
    m = prohibition
    p = 0
    c = c0+c2+c1
}
one sig rule3 extends Rule{}{
    s =s12
    t =r27
    m = permission
    p = 2
    c = c1+c2+c5+c7+c4
}
one sig rule4 extends Rule{}{
    s =s16
    t =r29
    m = permission
    p = 1
    c = c2+c8
}
one sig rule5 extends Rule{}{
    s =s0
    t =r2
    m = permission
    p = 1
    c = c0+c7+c4+c6+c5+c1
}
one sig rule6 extends Rule{}{
    s =s22
    t =r19
    m = permission
    p = 0
    c = c1+c4+c5
}
one sig rule7 extends Rule{}{
    s =s21
    t =r2
    m = prohibition
    p = 4
    c = c1+c9+c0
}
one sig rule8 extends Rule{}{
    s =s29
    t =r29
    m = permission
    p = 3
    c = c5+c8+c1
}
one sig rule9 extends Rule{}{
    s =s7
    t =r5
    m = prohibition
    p = 2
    c = c2+c7+c9
}
one sig rule10 extends Rule{}{
    s =s9
    t =r13
    m = prohibition
    p = 0
    c = c8
}
one sig rule11 extends Rule{}{
    s =s20
    t =r11
    m = permission
    p = 1
    c = c2+c6+c8
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
