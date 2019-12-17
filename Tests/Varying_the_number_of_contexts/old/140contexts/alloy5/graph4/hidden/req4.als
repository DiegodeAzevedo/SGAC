module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s7->s3+
         s7->s5+
         s7->s6+
         s8->s0+
         s8->s2+
         s8->s5+
         s8->s6+
         s9->s2+
         s9->s5+
         s9->s7+
         s10->s0+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s6+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s1+
         s12->s7+
         s12->s8+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s6+
         s13->s7+
         s13->s9+
         s13->s11+
         s14->s2+
         s14->s4+
         s14->s10+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s8+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s10+
         s16->s12+
         s16->s14+
         s16->s15+
         s17->s3+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s10+
         s17->s11+
         s17->s13+
         s17->s14+
         s18->s1+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s6+
         s18->s8+
         s18->s11+
         s18->s12+
         s18->s15+
         s18->s17+
         s19->s2+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s11+
         s19->s12+
         s19->s15+
         s19->s16+
         s19->s17+
         s19->s18+
         s20->s4+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s16+
         s20->s18+
         s21->s1+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s10+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s18+
         s22->s1+
         s22->s2+
         s22->s7+
         s22->s9+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s19+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s18+
         s23->s19+
         s23->s21+
         s23->s22+
         s24->s0+
         s24->s1+
         s24->s2+
         s24->s3+
         s24->s5+
         s24->s6+
         s24->s7+
         s24->s9+
         s24->s10+
         s24->s12+
         s24->s17+
         s24->s18+
         s24->s21+
         s24->s23+
         s25->s1+
         s25->s2+
         s25->s5+
         s25->s8+
         s25->s9+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s17+
         s25->s18+
         s25->s21+
         s25->s22+
         s25->s23+
         s26->s4+
         s26->s6+
         s26->s7+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s15+
         s26->s16+
         s26->s23+
         s26->s24+
         s27->s1+
         s27->s2+
         s27->s4+
         s27->s5+
         s27->s8+
         s27->s9+
         s27->s15+
         s27->s18+
         s27->s19+
         s27->s20+
         s27->s21+
         s27->s23+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s5+
         s28->s7+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s23+
         s28->s24+
         s28->s26+
         s29->s0+
         s29->s1+
         s29->s5+
         s29->s8+
         s29->s10+
         s29->s11+
         s29->s15+
         s29->s16+
         s29->s18+
         s29->s19+
         s29->s20+
         s29->s23+
         s29->s25+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r1->r0+
         r2->r0+
         r4->r0+
         r4->r1+
         r4->r3+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r2+
         r6->r3+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r6+
         r8->r5+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r2+
         r10->r5+
         r10->r6+
         r10->r9+
         r11->r0+
         r11->r2+
         r11->r4+
         r11->r5+
         r11->r10+
         r12->r0+
         r12->r6+
         r12->r7+
         r12->r10+
         r13->r0+
         r13->r4+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r11+
         r13->r12+
         r14->r0+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r10+
         r14->r11+
         r14->r12+
         r15->r0+
         r15->r2+
         r15->r6+
         r15->r11+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r5+
         r16->r6+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r14+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r4+
         r17->r6+
         r17->r10+
         r17->r12+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r1+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r7+
         r18->r10+
         r18->r12+
         r18->r15+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r12+
         r19->r13+
         r19->r14+
         r19->r18+
         r20->r0+
         r20->r2+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r14+
         r20->r18+
         r21->r0+
         r21->r2+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r10+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r16+
         r21->r18+
         r22->r2+
         r22->r3+
         r22->r4+
         r22->r8+
         r22->r10+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r7+
         r23->r11+
         r23->r14+
         r23->r16+
         r23->r19+
         r23->r20+
         r23->r21+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r7+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r19+
         r24->r21+
         r25->r0+
         r25->r3+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r14+
         r26->r15+
         r26->r17+
         r26->r19+
         r26->r23+
         r26->r24+
         r26->r25+
         r27->r2+
         r27->r4+
         r27->r7+
         r27->r9+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r14+
         r27->r16+
         r27->r20+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r1+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r14+
         r28->r15+
         r28->r22+
         r28->r23+
         r28->r26+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r8+
         r29->r10+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r20+
         r29->r24+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req4 extends Request{}{
sub=s4
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s17
    t =r21
    m = prohibition
    p = 1
    c = c7+c9+c0+c2+c3
}
one sig rule1 extends Rule{}{
    s =s11
    t =r18
    m = permission
    p = 2
    c = c7+c4+c6
}
one sig rule2 extends Rule{}{
    s =s22
    t =r18
    m = permission
    p = 0
    c = c2
}
one sig rule3 extends Rule{}{
    s =s22
    t =r18
    m = permission
    p = 1
    c = c3+c0+c1+c4
}
one sig rule4 extends Rule{}{
    s =s7
    t =r23
    m = permission
    p = 2
    c = c6
}
one sig rule5 extends Rule{}{
    s =s18
    t =r19
    m = permission
    p = 2
    c = c6+c9
}
one sig rule6 extends Rule{}{
    s =s4
    t =r5
    m = prohibition
    p = 4
    c = c1
}
one sig rule7 extends Rule{}{
    s =s18
    t =r17
    m = prohibition
    p = 1
    c = c5+c9+c3+c2+c0
}
one sig rule8 extends Rule{}{
    s =s22
    t =r20
    m = prohibition
    p = 4
    c = c2+c9
}
one sig rule9 extends Rule{}{
    s =s9
    t =r18
    m = prohibition
    p = 0
    c = c2+c6+c0+c1+c5+c8+c3
}
one sig rule10 extends Rule{}{
    s =s23
    t =r10
    m = prohibition
    p = 3
    c = c9+c0+c8
}
one sig rule11 extends Rule{}{
    s =s12
    t =r5
    m = permission
    p = 2
    c = c0+c6+c9
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
