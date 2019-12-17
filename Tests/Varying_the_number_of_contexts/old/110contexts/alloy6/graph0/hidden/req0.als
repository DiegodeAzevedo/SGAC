module filepath/param/graph/property/req
open filepath/alloy6/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s2+
         s4->s1+
         s5->s1+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s7->s5+
         s7->s6+
         s8->s2+
         s8->s3+
         s8->s4+
         s8->s6+
         s8->s7+
         s9->s1+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s1+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s5+
         s13->s7+
         s13->s12+
         s14->s0+
         s14->s3+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s12+
         s15->s1+
         s15->s7+
         s15->s8+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s7+
         s16->s11+
         s16->s13+
         s16->s15+
         s17->s1+
         s17->s2+
         s17->s5+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s10+
         s17->s13+
         s17->s15+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s7+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s17+
         s19->s1+
         s19->s4+
         s19->s9+
         s19->s10+
         s19->s11+
         s19->s13+
         s19->s15+
         s19->s16+
         s19->s17+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s11+
         s20->s14+
         s20->s18+
         s20->s19+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s5+
         s21->s6+
         s21->s9+
         s21->s10+
         s21->s13+
         s21->s14+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s18+
         s22->s19+
         s23->s0+
         s23->s3+
         s23->s5+
         s23->s6+
         s23->s8+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s1+
         s24->s7+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s22+
         s25->s1+
         s25->s4+
         s25->s5+
         s25->s6+
         s25->s7+
         s25->s9+
         s25->s10+
         s25->s12+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s18+
         s25->s20+
         s25->s21+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s2+
         s26->s3+
         s26->s9+
         s26->s10+
         s26->s11+
         s26->s17+
         s26->s21+
         s26->s22+
         s26->s24+
         s27->s0+
         s27->s2+
         s27->s5+
         s27->s7+
         s27->s8+
         s27->s12+
         s27->s16+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s24+
         s28->s0+
         s28->s3+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s11+
         s28->s13+
         s28->s16+
         s28->s18+
         s28->s21+
         s28->s23+
         s28->s24+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s4+
         s29->s8+
         s29->s11+
         s29->s12+
         s29->s13+
         s29->s16+
         s29->s20+
         s29->s21+
         s29->s22+
         s29->s23+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r1+
         r6->r3+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r3+
         r8->r4+
         r8->r5+
         r8->r6+
         r8->r7+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r5+
         r9->r6+
         r10->r2+
         r10->r3+
         r11->r1+
         r11->r4+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r9+
         r11->r10+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r2+
         r14->r3+
         r14->r5+
         r14->r7+
         r14->r8+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r6+
         r15->r10+
         r15->r11+
         r15->r12+
         r15->r13+
         r15->r14+
         r16->r2+
         r16->r3+
         r16->r4+
         r16->r6+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r4+
         r18->r5+
         r18->r8+
         r18->r11+
         r18->r13+
         r18->r16+
         r18->r17+
         r19->r0+
         r19->r1+
         r19->r2+
         r19->r6+
         r19->r8+
         r19->r9+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r9+
         r20->r11+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r17+
         r20->r18+
         r21->r2+
         r21->r3+
         r21->r4+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r14+
         r21->r16+
         r21->r18+
         r21->r19+
         r22->r0+
         r22->r3+
         r22->r4+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r13+
         r22->r14+
         r22->r16+
         r22->r18+
         r22->r21+
         r23->r1+
         r23->r3+
         r23->r8+
         r23->r9+
         r23->r11+
         r23->r12+
         r23->r16+
         r23->r17+
         r23->r19+
         r23->r20+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r10+
         r24->r13+
         r24->r14+
         r24->r16+
         r24->r19+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r1+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r9+
         r25->r14+
         r25->r18+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r0+
         r26->r1+
         r26->r6+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r14+
         r26->r17+
         r26->r18+
         r26->r21+
         r26->r23+
         r27->r2+
         r27->r4+
         r27->r9+
         r27->r10+
         r27->r15+
         r27->r18+
         r27->r19+
         r27->r21+
         r27->r23+
         r27->r24+
         r27->r25+
         r27->r26+
         r28->r0+
         r28->r3+
         r28->r4+
         r28->r5+
         r28->r7+
         r28->r9+
         r28->r10+
         r28->r11+
         r28->r14+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r23+
         r28->r24+
         r28->r25+
         r29->r0+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r9+
         r29->r11+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r18+
         r29->r19+
         r29->r23+
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
    s =s11
    t =r23
    m = permission
    p = 2
    c = c7+c3+c9+c0+c8+c1
}
one sig rule1 extends Rule{}{
    s =s2
    t =r5
    m = prohibition
    p = 1
    c = c2+c1+c8+c0+c4
}
one sig rule2 extends Rule{}{
    s =s0
    t =r26
    m = permission
    p = 0
    c = c5+c8+c4+c0
}
one sig rule3 extends Rule{}{
    s =s11
    t =r26
    m = prohibition
    p = 4
    c = c3+c1+c0+c7+c6+c5+c4
}
one sig rule4 extends Rule{}{
    s =s7
    t =r6
    m = permission
    p = 1
    c = c3
}
one sig rule5 extends Rule{}{
    s =s23
    t =r27
    m = prohibition
    p = 2
    c = c6+c9
}
one sig rule6 extends Rule{}{
    s =s27
    t =r24
    m = prohibition
    p = 0
    c = c2+c4+c3
}
one sig rule7 extends Rule{}{
    s =s9
    t =r1
    m = permission
    p = 2
    c = c3+c9+c7+c1
}
one sig rule8 extends Rule{}{
    s =s17
    t =r24
    m = permission
    p = 1
    c = c2+c5
}
one sig rule9 extends Rule{}{
    s =s28
    t =r21
    m = prohibition
    p = 4
    c = c2+c5+c0+c3+c1
}
one sig rule10 extends Rule{}{
    s =s0
    t =r13
    m = prohibition
    p = 0
    c = c9+c8+c6+c0
}
one sig rule11 extends Rule{}{
    s =s6
    t =r21
    m = prohibition
    p = 2
    c = c6+c8+c1+c4+c2+c5
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
