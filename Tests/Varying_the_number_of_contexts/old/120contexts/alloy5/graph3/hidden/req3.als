module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s2+
         s5->s3+
         s6->s3+
         s7->s1+
         s7->s2+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s3+
         s8->s5+
         s8->s7+
         s9->s0+
         s9->s2+
         s9->s7+
         s9->s8+
         s10->s1+
         s10->s2+
         s10->s4+
         s11->s3+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s2+
         s12->s3+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s6+
         s13->s8+
         s13->s9+
         s13->s11+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s9+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s5+
         s15->s8+
         s15->s10+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s13+
         s17->s1+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s13+
         s18->s15+
         s18->s17+
         s19->s1+
         s19->s4+
         s19->s5+
         s19->s6+
         s19->s9+
         s19->s12+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s2+
         s20->s4+
         s20->s7+
         s20->s9+
         s20->s10+
         s20->s12+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s17+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s3+
         s21->s6+
         s21->s8+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s16+
         s21->s17+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s7+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s15+
         s22->s16+
         s22->s18+
         s22->s20+
         s23->s2+
         s23->s5+
         s23->s8+
         s23->s9+
         s23->s12+
         s23->s15+
         s23->s16+
         s23->s19+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s10+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s16+
         s24->s17+
         s24->s20+
         s25->s0+
         s25->s1+
         s25->s3+
         s25->s8+
         s25->s9+
         s25->s11+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s1+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s20+
         s26->s23+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s7+
         s27->s11+
         s27->s12+
         s27->s13+
         s27->s16+
         s27->s21+
         s27->s23+
         s27->s26+
         s28->s1+
         s28->s2+
         s28->s9+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s24+
         s28->s25+
         s29->s1+
         s29->s2+
         s29->s4+
         s29->s6+
         s29->s7+
         s29->s12+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s22+
         s29->s25}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r4->r0+
         r6->r0+
         r6->r1+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r3+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r4+
         r11->r9+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r4+
         r12->r5+
         r12->r6+
         r13->r0+
         r13->r3+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r11+
         r14->r0+
         r14->r4+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r2+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r18->r1+
         r18->r2+
         r18->r4+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r15+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r11+
         r19->r13+
         r19->r15+
         r19->r18+
         r20->r0+
         r20->r2+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r17+
         r20->r18+
         r21->r1+
         r21->r5+
         r21->r6+
         r21->r11+
         r21->r12+
         r21->r14+
         r21->r16+
         r21->r17+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r2+
         r22->r3+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r3+
         r23->r4+
         r23->r6+
         r23->r13+
         r23->r14+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r20+
         r24->r22+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r10+
         r25->r13+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r23+
         r26->r1+
         r26->r5+
         r26->r6+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r17+
         r26->r20+
         r26->r21+
         r26->r23+
         r26->r24+
         r27->r0+
         r27->r1+
         r27->r3+
         r27->r4+
         r27->r5+
         r27->r10+
         r27->r13+
         r27->r17+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r5+
         r28->r7+
         r28->r10+
         r28->r13+
         r28->r14+
         r28->r15+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r22+
         r28->r24+
         r28->r26+
         r28->r27+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r18+
         r29->r19+
         r29->r20+
         r29->r22+
         r29->r23+
         r29->r25+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s0
res=r5
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s4
    t =r24
    m = prohibition
    p = 1
    c = c0+c5+c3+c9+c7
}
one sig rule1 extends Rule{}{
    s =s6
    t =r15
    m = prohibition
    p = 1
    c = c4+c7+c5
}
one sig rule2 extends Rule{}{
    s =s5
    t =r12
    m = permission
    p = 1
    c = c1+c6+c9+c3+c8
}
one sig rule3 extends Rule{}{
    s =s3
    t =r5
    m = prohibition
    p = 3
    c = c5+c3+c2+c1+c7
}
one sig rule4 extends Rule{}{
    s =s24
    t =r29
    m = permission
    p = 1
    c = c5+c4+c3+c0+c1
}
one sig rule5 extends Rule{}{
    s =s0
    t =r18
    m = permission
    p = 2
    c = c1+c7+c6
}
one sig rule6 extends Rule{}{
    s =s24
    t =r15
    m = permission
    p = 1
    c = c6+c8+c9+c3+c0+c2
}
one sig rule7 extends Rule{}{
    s =s25
    t =r10
    m = prohibition
    p = 1
    c = c4+c7+c6+c1+c9
}
one sig rule8 extends Rule{}{
    s =s14
    t =r14
    m = permission
    p = 0
    c = c7+c3+c5+c8+c9+c2
}
one sig rule9 extends Rule{}{
    s =s26
    t =r2
    m = permission
    p = 3
    c = c8+c6
}
one sig rule10 extends Rule{}{
    s =s13
    t =r26
    m = permission
    p = 3
    c = c1+c4+c5+c7
}
one sig rule11 extends Rule{}{
    s =s1
    t =r15
    m = permission
    p = 4
    c = c4+c6+c7
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
check HiddenDocument_r5_c0{ HiddenDocument[r5,c0]} for 4
check HiddenDocument_r5_c1{ HiddenDocument[r5,c1]} for 4
check HiddenDocument_r5_c2{ HiddenDocument[r5,c2]} for 4
check HiddenDocument_r5_c3{ HiddenDocument[r5,c3]} for 4
check HiddenDocument_r5_c4{ HiddenDocument[r5,c4]} for 4
check HiddenDocument_r5_c5{ HiddenDocument[r5,c5]} for 4
check HiddenDocument_r5_c6{ HiddenDocument[r5,c6]} for 4
check HiddenDocument_r5_c7{ HiddenDocument[r5,c7]} for 4
check HiddenDocument_r5_c8{ HiddenDocument[r5,c8]} for 4
check HiddenDocument_r5_c9{ HiddenDocument[r5,c9]} for 4
