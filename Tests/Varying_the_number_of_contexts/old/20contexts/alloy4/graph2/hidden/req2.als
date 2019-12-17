module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s1+
         s4->s0+
         s4->s2+
         s5->s1+
         s6->s1+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s6+
         s8->s1+
         s8->s2+
         s8->s3+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s2+
         s10->s4+
         s10->s8+
         s11->s2+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s9+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s11+
         s14->s0+
         s14->s2+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s11+
         s15->s12+
         s16->s0+
         s16->s4+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s15+
         s17->s1+
         s17->s5+
         s17->s7+
         s17->s10+
         s17->s14+
         s18->s0+
         s18->s1+
         s18->s3+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s17+
         s19->s1+
         s19->s2+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s13+
         s19->s14+
         s19->s18+
         s20->s4+
         s20->s5+
         s20->s8+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s17+
         s21->s2+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s12+
         s21->s14+
         s21->s16+
         s22->s0+
         s22->s2+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s16+
         s22->s18+
         s22->s19+
         s22->s21+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s18+
         s23->s19+
         s23->s22+
         s24->s2+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s18+
         s24->s21+
         s24->s22+
         s25->s2+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s11+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s22+
         s25->s23+
         s26->s3+
         s26->s6+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s17+
         s26->s19+
         s26->s21+
         s26->s22+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s6+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s16+
         s27->s20+
         s27->s23+
         s27->s24+
         s27->s26+
         s28->s2+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s9+
         s28->s11+
         s28->s13+
         s28->s18+
         s28->s23+
         s28->s24+
         s28->s27+
         s29->s1+
         s29->s5+
         s29->s8+
         s29->s10+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s16+
         s29->s19+
         s29->s21+
         s29->s22+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r7->r1+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r7+
         r9->r8+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r7+
         r11->r6+
         r11->r7+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r10+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r9+
         r13->r10+
         r14->r5+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r3+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r12+
         r16->r2+
         r16->r8+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r16+
         r19->r2+
         r19->r5+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r18+
         r20->r2+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r7+
         r21->r13+
         r21->r14+
         r21->r15+
         r22->r2+
         r22->r4+
         r22->r8+
         r22->r9+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r19+
         r22->r20+
         r23->r4+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r17+
         r23->r18+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r1+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r12+
         r24->r15+
         r24->r20+
         r24->r21+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r11+
         r25->r15+
         r25->r18+
         r25->r19+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r8+
         r26->r10+
         r26->r13+
         r26->r16+
         r26->r17+
         r26->r18+
         r26->r19+
         r27->r4+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r25+
         r27->r26+
         r28->r2+
         r28->r5+
         r28->r6+
         r28->r8+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r23+
         r28->r24+
         r28->r27+
         r29->r0+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r10+
         r29->r11+
         r29->r12+
         r29->r15+
         r29->r16+
         r29->r23+
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
    s =s29
    t =r4
    m = permission
    p = 0
    c = c3+c5
}
one sig rule1 extends Rule{}{
    s =s15
    t =r27
    m = permission
    p = 1
    c = c4+c2+c9+c0+c7+c3+c8
}
one sig rule2 extends Rule{}{
    s =s29
    t =r5
    m = permission
    p = 0
    c = c1
}
one sig rule3 extends Rule{}{
    s =s21
    t =r14
    m = prohibition
    p = 2
    c = c5+c8+c4+c1
}
one sig rule4 extends Rule{}{
    s =s26
    t =r22
    m = permission
    p = 4
    c = c0+c8+c5+c7+c1
}
one sig rule5 extends Rule{}{
    s =s4
    t =r2
    m = permission
    p = 4
    c = c0+c5+c2+c3+c1
}
one sig rule6 extends Rule{}{
    s =s2
    t =r5
    m = prohibition
    p = 1
    c = c0+c4+c8+c7+c2
}
one sig rule7 extends Rule{}{
    s =s22
    t =r14
    m = permission
    p = 3
    c = c8+c2+c9+c4
}
one sig rule8 extends Rule{}{
    s =s14
    t =r12
    m = permission
    p = 4
    c = c5+c1+c8
}
one sig rule9 extends Rule{}{
    s =s20
    t =r23
    m = prohibition
    p = 4
    c = c7+c2+c9
}
one sig rule10 extends Rule{}{
    s =s2
    t =r4
    m = prohibition
    p = 3
    c = c3+c0+c7+c6+c4+c5+c2
}
one sig rule11 extends Rule{}{
    s =s21
    t =r27
    m = permission
    p = 3
    c = c0+c8
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
