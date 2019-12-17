module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s4+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s5+
         s8->s0+
         s8->s1+
         s8->s3+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s0+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s10+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s9+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s5+
         s14->s10+
         s14->s12+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s9+
         s16->s11+
         s16->s15+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s16+
         s18->s1+
         s18->s2+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s17+
         s19->s4+
         s19->s6+
         s19->s11+
         s19->s12+
         s19->s14+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s0+
         s20->s3+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s16+
         s20->s18+
         s20->s19+
         s21->s3+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s18+
         s22->s3+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s10+
         s22->s13+
         s22->s15+
         s22->s17+
         s22->s18+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s21+
         s24->s1+
         s24->s2+
         s24->s4+
         s24->s5+
         s24->s7+
         s24->s8+
         s24->s9+
         s24->s10+
         s24->s11+
         s24->s14+
         s24->s16+
         s24->s18+
         s24->s20+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s13+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s1+
         s26->s2+
         s26->s4+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s13+
         s26->s17+
         s26->s20+
         s26->s21+
         s26->s23+
         s26->s24+
         s27->s0+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s10+
         s27->s13+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s4+
         s28->s6+
         s28->s10+
         s28->s11+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s18+
         s28->s19+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s13+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s25+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r0+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r2+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r5+
         r8->r6+
         r9->r0+
         r9->r6+
         r9->r7+
         r10->r3+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r3+
         r11->r5+
         r11->r6+
         r12->r0+
         r12->r1+
         r12->r3+
         r12->r5+
         r12->r6+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r7+
         r13->r8+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r1+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r9+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r7+
         r16->r10+
         r16->r12+
         r16->r14+
         r17->r4+
         r17->r6+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r12+
         r17->r13+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r19->r0+
         r19->r1+
         r19->r4+
         r19->r7+
         r19->r9+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r18+
         r20->r2+
         r20->r4+
         r20->r14+
         r20->r16+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r8+
         r21->r9+
         r21->r10+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r16+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r2+
         r22->r5+
         r22->r6+
         r22->r10+
         r22->r11+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r19+
         r22->r20+
         r23->r0+
         r23->r5+
         r23->r6+
         r23->r7+
         r23->r13+
         r23->r15+
         r23->r16+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r11+
         r24->r12+
         r24->r14+
         r24->r20+
         r24->r21+
         r25->r0+
         r25->r1+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r12+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r2+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r15+
         r26->r20+
         r26->r21+
         r26->r24+
         r27->r0+
         r27->r5+
         r27->r7+
         r27->r9+
         r27->r11+
         r27->r12+
         r27->r13+
         r27->r14+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r24+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r11+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r22+
         r28->r24+
         r28->r25+
         r28->r27+
         r29->r0+
         r29->r1+
         r29->r2+
         r29->r5+
         r29->r7+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r15+
         r29->r17+
         r29->r26+
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
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s27
    t =r18
    m = permission
    p = 3
    c = c8+c6+c4
}
one sig rule1 extends Rule{}{
    s =s10
    t =r1
    m = prohibition
    p = 0
    c = c2+c5+c8+c0+c9+c1+c3
}
one sig rule2 extends Rule{}{
    s =s16
    t =r10
    m = permission
    p = 0
    c = c1
}
one sig rule3 extends Rule{}{
    s =s24
    t =r4
    m = permission
    p = 0
    c = c5+c2+c1+c4+c3+c0
}
one sig rule4 extends Rule{}{
    s =s9
    t =r20
    m = permission
    p = 4
    c = c8
}
one sig rule5 extends Rule{}{
    s =s29
    t =r27
    m = prohibition
    p = 3
    c = c7+c1+c4+c0+c3
}
one sig rule6 extends Rule{}{
    s =s22
    t =r5
    m = permission
    p = 2
    c = c2+c7+c0
}
one sig rule7 extends Rule{}{
    s =s21
    t =r12
    m = permission
    p = 2
    c = c8+c4+c3+c1+c7
}
one sig rule8 extends Rule{}{
    s =s10
    t =r29
    m = prohibition
    p = 3
    c = c6+c0+c9+c5
}
one sig rule9 extends Rule{}{
    s =s27
    t =r10
    m = prohibition
    p = 0
    c = c1+c3+c2
}
one sig rule10 extends Rule{}{
    s =s16
    t =r17
    m = permission
    p = 4
    c = c8+c6+c4+c0+c7
}
one sig rule11 extends Rule{}{
    s =s18
    t =r12
    m = prohibition
    p = 0
    c = c8
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
