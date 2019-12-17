module filepath/param/graph/property/req
open filepath/alloy3/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s2+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s5+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s5+
         s9->s8+
         s10->s2+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s9+
         s11->s1+
         s11->s3+
         s11->s5+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s6+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s4+
         s13->s5+
         s13->s8+
         s13->s9+
         s14->s0+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s12+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s6+
         s15->s9+
         s15->s11+
         s15->s12+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s9+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s3+
         s17->s5+
         s17->s7+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s4+
         s18->s5+
         s18->s9+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s9+
         s19->s12+
         s19->s14+
         s19->s17+
         s20->s0+
         s20->s4+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s17+
         s20->s18+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s16+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s2+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s10+
         s22->s13+
         s22->s14+
         s22->s15+
         s22->s17+
         s22->s21+
         s23->s0+
         s23->s2+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s17+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s9+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s19+
         s24->s21+
         s25->s0+
         s25->s1+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s23+
         s26->s0+
         s26->s2+
         s26->s3+
         s26->s4+
         s26->s5+
         s26->s7+
         s26->s10+
         s26->s12+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s20+
         s26->s22+
         s26->s24+
         s26->s25+
         s27->s2+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s20+
         s27->s22+
         s27->s24+
         s27->s25+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s21+
         s28->s24+
         s28->s25+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s14+
         s29->s15+
         s29->s18+
         s29->s20+
         s29->s23+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r2->r1+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r5->r2+
         r5->r3+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r4+
         r6->r5+
         r7->r0+
         r7->r3+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r3+
         r8->r5+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r2+
         r10->r4+
         r10->r6+
         r10->r7+
         r10->r8+
         r11->r4+
         r11->r7+
         r12->r1+
         r12->r3+
         r12->r8+
         r13->r0+
         r13->r1+
         r13->r2+
         r13->r5+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r3+
         r14->r4+
         r14->r7+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r3+
         r15->r9+
         r15->r10+
         r16->r0+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r15+
         r17->r4+
         r17->r8+
         r17->r9+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r8+
         r18->r10+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r16+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r13+
         r20->r15+
         r20->r16+
         r20->r17+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r13+
         r21->r15+
         r21->r16+
         r21->r17+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r20+
         r22->r21+
         r23->r6+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r12+
         r23->r14+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r15+
         r24->r17+
         r24->r18+
         r24->r19+
         r24->r21+
         r24->r22+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r10+
         r25->r11+
         r25->r13+
         r25->r16+
         r25->r17+
         r25->r19+
         r25->r21+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r2+
         r26->r4+
         r26->r6+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r20+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r1+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r21+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r11+
         r28->r14+
         r28->r15+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r23+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r11+
         r29->r14+
         r29->r16+
         r29->r21+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s20
    t =r14
    m = permission
    p = 3
    c = c3+c5+c0+c4+c7
}
one sig rule1 extends Rule{}{
    s =s1
    t =r4
    m = prohibition
    p = 1
    c = c5+c2+c8+c9+c1+c0
}
one sig rule2 extends Rule{}{
    s =s18
    t =r17
    m = permission
    p = 0
    c = c2+c5+c4
}
one sig rule3 extends Rule{}{
    s =s16
    t =r11
    m = prohibition
    p = 3
    c = c0+c3+c6+c8+c7
}
one sig rule4 extends Rule{}{
    s =s17
    t =r16
    m = prohibition
    p = 4
    c = c3+c5+c4+c8+c9+c7
}
one sig rule5 extends Rule{}{
    s =s8
    t =r16
    m = prohibition
    p = 4
    c = c7+c9+c3+c4+c5
}
one sig rule6 extends Rule{}{
    s =s9
    t =r4
    m = prohibition
    p = 1
    c = c4+c7+c6+c1+c9+c2+c3
}
one sig rule7 extends Rule{}{
    s =s15
    t =r2
    m = prohibition
    p = 2
    c = c0+c3+c1+c6+c7+c5
}
one sig rule8 extends Rule{}{
    s =s1
    t =r13
    m = permission
    p = 0
    c = c9+c5+c7+c4+c2+c8+c0
}
one sig rule9 extends Rule{}{
    s =s8
    t =r14
    m = permission
    p = 0
    c = c6+c5+c0+c9+c2
}
one sig rule10 extends Rule{}{
    s =s21
    t =r5
    m = prohibition
    p = 4
    c = c5+c8+c7+c3+c4+c6
}
one sig rule11 extends Rule{}{
    s =s8
    t =r16
    m = permission
    p = 3
    c = c2+c4
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
