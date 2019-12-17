module filepath/param/graph/property/req
open filepath/alloy7/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s4->s1+
         s4->s3+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s4+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s3+
         s8->s4+
         s8->s5+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s6+
         s9->s8+
         s10->s1+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s7+
         s11->s9+
         s12->s0+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s5+
         s13->s7+
         s13->s9+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s8+
         s14->s9+
         s14->s11+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s11+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s0+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s9+
         s17->s13+
         s17->s14+
         s17->s16+
         s18->s0+
         s18->s1+
         s18->s7+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s1+
         s19->s4+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s11+
         s19->s12+
         s19->s14+
         s20->s9+
         s20->s11+
         s20->s13+
         s20->s14+
         s20->s15+
         s20->s16+
         s20->s19+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s12+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s13+
         s22->s15+
         s22->s18+
         s22->s20+
         s23->s0+
         s23->s2+
         s23->s3+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s18+
         s24->s0+
         s24->s3+
         s24->s7+
         s24->s8+
         s24->s12+
         s24->s16+
         s24->s18+
         s24->s19+
         s24->s21+
         s24->s23+
         s25->s1+
         s25->s6+
         s25->s7+
         s25->s8+
         s25->s9+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s16+
         s25->s17+
         s25->s21+
         s25->s23+
         s26->s0+
         s26->s3+
         s26->s4+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s14+
         s26->s17+
         s26->s19+
         s26->s22+
         s26->s25+
         s27->s2+
         s27->s4+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s14+
         s27->s15+
         s27->s17+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s24+
         s27->s26+
         s28->s0+
         s28->s2+
         s28->s3+
         s28->s4+
         s28->s5+
         s28->s9+
         s28->s10+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s17+
         s28->s18+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s14+
         s29->s23+
         s29->s24+
         s29->s26+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r3->r1+
         r3->r2+
         r4->r1+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r6->r5+
         r7->r1+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r6+
         r10->r9+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r5+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r3+
         r12->r6+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r8+
         r15->r9+
         r15->r10+
         r15->r13+
         r15->r14+
         r16->r0+
         r16->r1+
         r16->r3+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r5+
         r17->r8+
         r17->r12+
         r17->r13+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r14+
         r19->r15+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r10+
         r20->r11+
         r20->r18+
         r21->r1+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r8+
         r21->r10+
         r21->r13+
         r21->r15+
         r21->r18+
         r21->r19+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r5+
         r22->r9+
         r22->r11+
         r22->r12+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r8+
         r23->r9+
         r23->r12+
         r23->r14+
         r23->r15+
         r23->r20+
         r23->r21+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r9+
         r24->r11+
         r24->r13+
         r24->r16+
         r24->r17+
         r24->r23+
         r25->r0+
         r25->r3+
         r25->r4+
         r25->r7+
         r25->r8+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r13+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r21+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r11+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r23+
         r27->r1+
         r27->r4+
         r27->r6+
         r27->r7+
         r27->r8+
         r27->r9+
         r27->r10+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r20+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r8+
         r28->r10+
         r28->r11+
         r28->r12+
         r28->r15+
         r28->r16+
         r28->r17+
         r28->r18+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r26+
         r29->r0+
         r29->r3+
         r29->r8+
         r29->r11+
         r29->r12+
         r29->r16+
         r29->r18+
         r29->r23+
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
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s16
    t =r9
    m = permission
    p = 1
    c = c3+c6+c4
}
one sig rule1 extends Rule{}{
    s =s26
    t =r3
    m = permission
    p = 0
    c = c6+c8+c9+c4+c1+c2
}
one sig rule2 extends Rule{}{
    s =s15
    t =r0
    m = permission
    p = 1
    c = c9+c4
}
one sig rule3 extends Rule{}{
    s =s25
    t =r17
    m = prohibition
    p = 4
    c = c7
}
one sig rule4 extends Rule{}{
    s =s7
    t =r22
    m = prohibition
    p = 1
    c = c1
}
one sig rule5 extends Rule{}{
    s =s4
    t =r29
    m = prohibition
    p = 1
    c = c6+c7+c0+c9+c8+c1
}
one sig rule6 extends Rule{}{
    s =s13
    t =r21
    m = permission
    p = 3
    c = c5+c8+c7+c1+c2
}
one sig rule7 extends Rule{}{
    s =s12
    t =r14
    m = prohibition
    p = 0
    c = c5+c0+c7+c1
}
one sig rule8 extends Rule{}{
    s =s8
    t =r7
    m = permission
    p = 4
    c = c0+c4+c5
}
one sig rule9 extends Rule{}{
    s =s16
    t =r11
    m = permission
    p = 3
    c = c0+c5+c8+c3+c4+c6
}
one sig rule10 extends Rule{}{
    s =s4
    t =r3
    m = permission
    p = 1
    c = c2+c7+c8+c6+c0+c4
}
one sig rule11 extends Rule{}{
    s =s17
    t =r27
    m = permission
    p = 3
    c = c6+c8+c7
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
