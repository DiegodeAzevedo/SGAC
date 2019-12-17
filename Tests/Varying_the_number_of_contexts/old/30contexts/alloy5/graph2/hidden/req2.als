module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s4->s0+
         s4->s1+
         s5->s1+
         s5->s3+
         s5->s4+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s5+
         s8->s6+
         s9->s1+
         s9->s3+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s1+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s5+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s7+
         s14->s10+
         s14->s12+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s6+
         s15->s8+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s16->s15+
         s17->s0+
         s17->s4+
         s17->s9+
         s17->s10+
         s17->s12+
         s17->s13+
         s18->s2+
         s18->s9+
         s18->s11+
         s18->s13+
         s18->s14+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s3+
         s20->s5+
         s20->s11+
         s20->s15+
         s20->s19+
         s21->s0+
         s21->s4+
         s21->s7+
         s21->s8+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s17+
         s22->s2+
         s22->s3+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s14+
         s22->s17+
         s22->s19+
         s22->s20+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s6+
         s23->s9+
         s23->s11+
         s23->s13+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s3+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s12+
         s24->s15+
         s24->s18+
         s24->s21+
         s24->s22+
         s25->s1+
         s25->s3+
         s25->s4+
         s25->s8+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s21+
         s25->s22+
         s25->s24+
         s26->s0+
         s26->s5+
         s26->s7+
         s26->s8+
         s26->s9+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s17+
         s26->s19+
         s26->s20+
         s26->s21+
         s26->s22+
         s26->s23+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s7+
         s27->s9+
         s27->s10+
         s27->s18+
         s27->s21+
         s27->s22+
         s27->s24+
         s27->s26+
         s28->s1+
         s28->s4+
         s28->s6+
         s28->s9+
         s28->s12+
         s28->s14+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s22+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s10+
         s29->s13+
         s29->s15+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s23+
         s29->s24+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r4->r0+
         r5->r0+
         r5->r2+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r4+
         r10->r2+
         r10->r3+
         r10->r6+
         r11->r3+
         r11->r4+
         r11->r5+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r8+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r7+
         r13->r10+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r12+
         r15->r0+
         r15->r11+
         r15->r12+
         r15->r14+
         r16->r0+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r4+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r12+
         r18->r13+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r13+
         r19->r14+
         r19->r16+
         r20->r1+
         r20->r2+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r14+
         r20->r16+
         r20->r19+
         r21->r3+
         r21->r7+
         r21->r9+
         r21->r12+
         r21->r14+
         r21->r17+
         r21->r18+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r5+
         r22->r6+
         r22->r9+
         r22->r12+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r21+
         r23->r1+
         r23->r2+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r9+
         r23->r10+
         r23->r14+
         r23->r16+
         r23->r19+
         r24->r1+
         r24->r4+
         r24->r8+
         r24->r9+
         r24->r14+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r5+
         r25->r7+
         r25->r8+
         r25->r12+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r21+
         r26->r24+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r26+
         r28->r2+
         r28->r4+
         r28->r7+
         r28->r10+
         r28->r12+
         r28->r13+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r23+
         r28->r24+
         r28->r27+
         r29->r2+
         r29->r5+
         r29->r8+
         r29->r11+
         r29->r16+
         r29->r17+
         r29->r20+
         r29->r21+
         r29->r22+
         r29->r25+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req2 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s20
    t =r25
    m = prohibition
    p = 2
    c = c6+c3+c8+c4+c9+c5
}
one sig rule1 extends Rule{}{
    s =s13
    t =r15
    m = permission
    p = 3
    c = c5+c1+c2
}
one sig rule2 extends Rule{}{
    s =s5
    t =r26
    m = prohibition
    p = 2
    c = c8+c1+c6+c7+c5+c3
}
one sig rule3 extends Rule{}{
    s =s5
    t =r25
    m = prohibition
    p = 2
    c = c5+c0+c9+c8+c7+c4+c3
}
one sig rule4 extends Rule{}{
    s =s10
    t =r16
    m = permission
    p = 2
    c = c2+c9
}
one sig rule5 extends Rule{}{
    s =s18
    t =r20
    m = permission
    p = 4
    c = c5+c1+c7
}
one sig rule6 extends Rule{}{
    s =s24
    t =r9
    m = prohibition
    p = 0
    c = c3+c1+c6+c5+c8+c2
}
one sig rule7 extends Rule{}{
    s =s7
    t =r24
    m = permission
    p = 2
    c = c8+c3+c9+c6
}
one sig rule8 extends Rule{}{
    s =s24
    t =r23
    m = permission
    p = 4
    c = c1+c0+c9+c3+c7
}
one sig rule9 extends Rule{}{
    s =s8
    t =r20
    m = permission
    p = 3
    c = c6+c4+c0+c3+c7
}
one sig rule10 extends Rule{}{
    s =s11
    t =r8
    m = prohibition
    p = 1
    c = c4+c1+c3
}
one sig rule11 extends Rule{}{
    s =s0
    t =r0
    m = prohibition
    p = 3
    c = c6+c7+c9
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
