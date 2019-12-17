module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s4->s0+
         s4->s1+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s5+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s4+
         s10->s2+
         s10->s4+
         s10->s6+
         s10->s8+
         s10->s9+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s12->s0+
         s12->s2+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s3+
         s13->s9+
         s13->s11+
         s13->s12+
         s14->s3+
         s14->s6+
         s14->s8+
         s14->s10+
         s14->s13+
         s15->s1+
         s15->s3+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s10+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s11+
         s17->s2+
         s17->s3+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s19->s17+
         s20->s0+
         s20->s5+
         s20->s7+
         s20->s9+
         s20->s11+
         s20->s15+
         s20->s16+
         s20->s17+
         s20->s18+
         s21->s1+
         s21->s5+
         s21->s13+
         s21->s16+
         s21->s17+
         s21->s20+
         s22->s0+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s16+
         s22->s17+
         s22->s18+
         s22->s19+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s4+
         s23->s7+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s8+
         s24->s11+
         s24->s15+
         s24->s17+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s22+
         s25->s3+
         s25->s5+
         s25->s11+
         s25->s12+
         s25->s19+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s10+
         s26->s14+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s23+
         s26->s24+
         s27->s1+
         s27->s3+
         s27->s6+
         s27->s13+
         s27->s18+
         s27->s19+
         s27->s22+
         s27->s24+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s22+
         s28->s23+
         s28->s26+
         s29->s0+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s10+
         s29->s12+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s22+
         s29->s23+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r4+
         r6->r5+
         r7->r0+
         r7->r1+
         r7->r3+
         r7->r4+
         r8->r1+
         r8->r2+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r4+
         r11->r7+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r5+
         r13->r12+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r13+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r9+
         r15->r10+
         r15->r13+
         r16->r2+
         r16->r4+
         r16->r6+
         r16->r10+
         r16->r12+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r10+
         r18->r11+
         r18->r13+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r5+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r14+
         r19->r15+
         r19->r17+
         r20->r0+
         r20->r2+
         r20->r5+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r7+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r21->r18+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r11+
         r22->r14+
         r22->r15+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r2+
         r23->r6+
         r23->r7+
         r23->r9+
         r23->r16+
         r23->r17+
         r23->r18+
         r23->r22+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r18+
         r24->r23+
         r25->r0+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r10+
         r25->r12+
         r25->r13+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r22+
         r25->r24+
         r26->r3+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r9+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r17+
         r26->r18+
         r26->r23+
         r26->r24+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r6+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r24+
         r28->r25+
         r29->r1+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r18+
         r29->r20+
         r29->r24+
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
one sig req1 extends Request{}{
sub=s0
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s7
    t =r16
    m = prohibition
    p = 3
    c = c7+c2+c0+c1+c6
}
one sig rule1 extends Rule{}{
    s =s5
    t =r4
    m = prohibition
    p = 4
    c = c8+c0+c9
}
one sig rule2 extends Rule{}{
    s =s9
    t =r8
    m = prohibition
    p = 4
    c = c7+c8+c1
}
one sig rule3 extends Rule{}{
    s =s6
    t =r12
    m = permission
    p = 3
    c = c4+c2+c5+c7+c9
}
one sig rule4 extends Rule{}{
    s =s21
    t =r20
    m = prohibition
    p = 2
    c = c0+c4+c7+c3+c8+c9+c5
}
one sig rule5 extends Rule{}{
    s =s26
    t =r26
    m = permission
    p = 0
    c = c7
}
one sig rule6 extends Rule{}{
    s =s28
    t =r7
    m = permission
    p = 3
    c = c6+c3+c9+c4+c8+c1
}
one sig rule7 extends Rule{}{
    s =s28
    t =r26
    m = prohibition
    p = 3
    c = c4+c5+c9+c8+c6
}
one sig rule8 extends Rule{}{
    s =s14
    t =r17
    m = prohibition
    p = 2
    c = c4+c0+c5
}
one sig rule9 extends Rule{}{
    s =s3
    t =r19
    m = prohibition
    p = 2
    c = c6+c7+c2+c5
}
one sig rule10 extends Rule{}{
    s =s8
    t =r5
    m = prohibition
    p = 4
    c = c6+c8+c7+c2
}
one sig rule11 extends Rule{}{
    s =s15
    t =r1
    m = permission
    p = 0
    c = c2+c0+c8
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
