module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s1+
         s3->s2+
         s4->s0+
         s5->s0+
         s5->s1+
         s6->s1+
         s6->s2+
         s6->s3+
         s7->s1+
         s7->s3+
         s7->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s4+
         s9->s6+
         s9->s7+
         s10->s8+
         s11->s1+
         s11->s2+
         s11->s4+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s3+
         s12->s5+
         s12->s9+
         s13->s0+
         s13->s1+
         s13->s4+
         s13->s7+
         s13->s10+
         s13->s11+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s10+
         s14->s13+
         s15->s0+
         s15->s3+
         s15->s7+
         s15->s12+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s11+
         s17->s12+
         s17->s14+
         s17->s16+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s19->s1+
         s19->s2+
         s19->s4+
         s19->s9+
         s19->s11+
         s19->s13+
         s19->s14+
         s19->s17+
         s20->s2+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s10+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s18+
         s21->s0+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s17+
         s21->s18+
         s21->s20+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s16+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s18+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s3+
         s24->s4+
         s24->s11+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s17+
         s24->s20+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s15+
         s25->s18+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s1+
         s26->s2+
         s26->s3+
         s26->s7+
         s26->s12+
         s26->s14+
         s26->s16+
         s26->s19+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s8+
         s27->s10+
         s27->s13+
         s27->s14+
         s27->s19+
         s27->s21+
         s27->s23+
         s27->s26+
         s28->s1+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s8+
         s28->s10+
         s28->s11+
         s28->s13+
         s28->s17+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s12+
         s29->s14+
         s29->s19+
         s29->s23+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r1+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r4+
         r6->r5+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r0+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r7+
         r11->r10+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r6+
         r12->r7+
         r12->r9+
         r13->r0+
         r13->r1+
         r13->r5+
         r13->r6+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r10+
         r15->r2+
         r15->r3+
         r15->r6+
         r15->r8+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r9+
         r16->r10+
         r16->r13+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r8+
         r18->r9+
         r18->r14+
         r18->r17+
         r19->r0+
         r19->r3+
         r19->r7+
         r19->r8+
         r19->r11+
         r19->r12+
         r19->r15+
         r19->r16+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r9+
         r20->r12+
         r20->r16+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r18+
         r22->r21+
         r23->r2+
         r23->r4+
         r23->r7+
         r23->r9+
         r23->r11+
         r23->r13+
         r23->r14+
         r23->r15+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r6+
         r24->r8+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r13+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r21+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r8+
         r25->r9+
         r25->r11+
         r25->r13+
         r25->r17+
         r25->r19+
         r25->r20+
         r25->r22+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r7+
         r26->r14+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r20+
         r26->r21+
         r27->r4+
         r27->r7+
         r27->r8+
         r27->r11+
         r27->r12+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r23+
         r27->r25+
         r28->r0+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r8+
         r28->r9+
         r28->r12+
         r28->r14+
         r28->r17+
         r28->r19+
         r28->r23+
         r28->r24+
         r28->r27+
         r29->r1+
         r29->r2+
         r29->r5+
         r29->r7+
         r29->r10+
         r29->r11+
         r29->r14+
         r29->r20+
         r29->r22+
         r29->r23+
         r29->r24+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s1
res=r3
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s1
    t =r16
    m = permission
    p = 1
    c = c2
}
one sig rule1 extends Rule{}{
    s =s23
    t =r0
    m = prohibition
    p = 4
    c = c3+c6+c4+c1+c7
}
one sig rule2 extends Rule{}{
    s =s23
    t =r6
    m = prohibition
    p = 2
    c = c7+c6+c5+c0+c2
}
one sig rule3 extends Rule{}{
    s =s22
    t =r24
    m = permission
    p = 0
    c = c5
}
one sig rule4 extends Rule{}{
    s =s3
    t =r26
    m = prohibition
    p = 3
    c = c4+c2+c9+c7+c1+c5
}
one sig rule5 extends Rule{}{
    s =s1
    t =r25
    m = permission
    p = 1
    c = c0+c5+c7+c4+c8
}
one sig rule6 extends Rule{}{
    s =s3
    t =r22
    m = prohibition
    p = 2
    c = c7+c1
}
one sig rule7 extends Rule{}{
    s =s24
    t =r29
    m = permission
    p = 4
    c = c7+c4+c6+c9+c8+c5+c3
}
one sig rule8 extends Rule{}{
    s =s6
    t =r5
    m = prohibition
    p = 4
    c = c6+c1+c9
}
one sig rule9 extends Rule{}{
    s =s9
    t =r28
    m = prohibition
    p = 0
    c = c7+c1
}
one sig rule10 extends Rule{}{
    s =s10
    t =r4
    m = permission
    p = 4
    c = c5+c1+c6+c8
}
one sig rule11 extends Rule{}{
    s =s24
    t =r12
    m = permission
    p = 2
    c = c0+c2+c4+c9
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
check HiddenDocument_r3_c0{ HiddenDocument[r3,c0]} for 4
check HiddenDocument_r3_c1{ HiddenDocument[r3,c1]} for 4
check HiddenDocument_r3_c2{ HiddenDocument[r3,c2]} for 4
check HiddenDocument_r3_c3{ HiddenDocument[r3,c3]} for 4
check HiddenDocument_r3_c4{ HiddenDocument[r3,c4]} for 4
check HiddenDocument_r3_c5{ HiddenDocument[r3,c5]} for 4
check HiddenDocument_r3_c6{ HiddenDocument[r3,c6]} for 4
check HiddenDocument_r3_c7{ HiddenDocument[r3,c7]} for 4
check HiddenDocument_r3_c8{ HiddenDocument[r3,c8]} for 4
check HiddenDocument_r3_c9{ HiddenDocument[r3,c9]} for 4
