module filepath/param/graph/property/req
open filepath/alloy10/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s2->s0+
         s3->s0+
         s4->s3+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s6->s5+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s4+
         s8->s7+
         s9->s1+
         s9->s3+
         s9->s4+
         s9->s5+
         s9->s6+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s3+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s3+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s5+
         s12->s9+
         s12->s11+
         s13->s2+
         s13->s5+
         s13->s8+
         s13->s10+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s4+
         s15->s5+
         s15->s6+
         s15->s8+
         s15->s11+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s2+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s1+
         s18->s3+
         s18->s4+
         s18->s5+
         s18->s8+
         s18->s11+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s1+
         s19->s6+
         s19->s7+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s13+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s0+
         s20->s2+
         s20->s7+
         s20->s9+
         s20->s17+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s13+
         s21->s17+
         s21->s18+
         s21->s19+
         s22->s0+
         s22->s1+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s12+
         s22->s20+
         s22->s21+
         s23->s0+
         s23->s5+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s12+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s17+
         s23->s20+
         s23->s22+
         s24->s6+
         s24->s11+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s18+
         s24->s19+
         s24->s20+
         s24->s21+
         s25->s1+
         s25->s2+
         s25->s4+
         s25->s7+
         s25->s8+
         s25->s17+
         s25->s18+
         s25->s21+
         s25->s22+
         s26->s6+
         s26->s13+
         s26->s14+
         s26->s18+
         s26->s23+
         s27->s2+
         s27->s4+
         s27->s5+
         s27->s6+
         s27->s7+
         s27->s8+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s18+
         s27->s21+
         s27->s22+
         s27->s23+
         s27->s24+
         s28->s0+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s10+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s23+
         s29->s1+
         s29->s2+
         s29->s5+
         s29->s8+
         s29->s9+
         s29->s10+
         s29->s11+
         s29->s15+
         s29->s16+
         s29->s17+
         s29->s19+
         s29->s20+
         s29->s21+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r3->r1+
         r4->r1+
         r4->r3+
         r5->r0+
         r5->r1+
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
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r2+
         r8->r3+
         r9->r0+
         r9->r1+
         r9->r3+
         r9->r4+
         r9->r5+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r8+
         r11->r3+
         r11->r6+
         r11->r7+
         r11->r8+
         r11->r10+
         r12->r0+
         r12->r3+
         r12->r4+
         r12->r6+
         r12->r8+
         r13->r0+
         r13->r3+
         r13->r7+
         r13->r8+
         r13->r10+
         r13->r11+
         r14->r1+
         r14->r3+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r12+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r7+
         r15->r9+
         r15->r10+
         r15->r13+
         r16->r0+
         r16->r3+
         r16->r4+
         r17->r0+
         r17->r1+
         r17->r4+
         r17->r8+
         r17->r10+
         r17->r12+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r2+
         r18->r12+
         r18->r16+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r9+
         r19->r13+
         r19->r14+
         r19->r16+
         r19->r18+
         r20->r1+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r8+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r15+
         r20->r18+
         r21->r0+
         r21->r2+
         r21->r6+
         r21->r7+
         r21->r12+
         r21->r14+
         r21->r18+
         r21->r19+
         r22->r2+
         r22->r4+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r9+
         r22->r16+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r0+
         r23->r1+
         r23->r2+
         r23->r4+
         r23->r5+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r13+
         r23->r16+
         r23->r18+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r9+
         r24->r15+
         r24->r17+
         r24->r18+
         r24->r20+
         r25->r2+
         r25->r3+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r8+
         r25->r11+
         r25->r14+
         r25->r15+
         r25->r22+
         r25->r23+
         r26->r4+
         r26->r6+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r22+
         r26->r23+
         r27->r2+
         r27->r3+
         r27->r4+
         r27->r6+
         r27->r12+
         r27->r14+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r23+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r14+
         r28->r17+
         r28->r18+
         r28->r22+
         r28->r23+
         r28->r25+
         r28->r26+
         r29->r0+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r12+
         r29->r16+
         r29->r21+
         r29->r23+
         r29->r26+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req6 extends Request{}{
sub=s5
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s14
    t =r0
    m = prohibition
    p = 4
    c = c8
}
one sig rule1 extends Rule{}{
    s =s19
    t =r11
    m = prohibition
    p = 1
    c = c6+c4+c8+c9
}
one sig rule2 extends Rule{}{
    s =s25
    t =r9
    m = prohibition
    p = 1
    c = c4+c0+c6+c7+c2+c9
}
one sig rule3 extends Rule{}{
    s =s3
    t =r0
    m = permission
    p = 3
    c = c5+c0+c3+c2
}
one sig rule4 extends Rule{}{
    s =s10
    t =r29
    m = permission
    p = 2
    c = c8+c4+c0+c1+c2
}
one sig rule5 extends Rule{}{
    s =s20
    t =r22
    m = prohibition
    p = 1
    c = c5+c2+c9+c8+c3
}
one sig rule6 extends Rule{}{
    s =s7
    t =r23
    m = prohibition
    p = 3
    c = c3+c1+c5+c0+c9
}
one sig rule7 extends Rule{}{
    s =s7
    t =r2
    m = permission
    p = 4
    c = c8+c5+c7+c3+c6
}
one sig rule8 extends Rule{}{
    s =s28
    t =r5
    m = permission
    p = 1
    c = c8+c5+c2+c3+c6+c4+c1
}
one sig rule9 extends Rule{}{
    s =s8
    t =r3
    m = prohibition
    p = 4
    c = c0
}
one sig rule10 extends Rule{}{
    s =s19
    t =r4
    m = permission
    p = 1
    c = c1+c0+c9+c7+c8+c4+c6+c3
}
one sig rule11 extends Rule{}{
    s =s11
    t =r16
    m = permission
    p = 3
    c = c1
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
