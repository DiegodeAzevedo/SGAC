module filepath/param/graph/property/req
open filepath/alloy9/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s4->s0+
         s4->s1+
         s4->s3+
         s5->s2+
         s6->s1+
         s6->s2+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s5+
         s7->s6+
         s8->s6+
         s9->s1+
         s9->s3+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s2+
         s10->s5+
         s10->s7+
         s10->s8+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s2+
         s12->s4+
         s12->s6+
         s12->s7+
         s12->s8+
         s12->s9+
         s12->s10+
         s12->s11+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s7+
         s13->s9+
         s13->s10+
         s13->s12+
         s14->s0+
         s14->s1+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s9+
         s14->s13+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s9+
         s16->s10+
         s16->s13+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s11+
         s17->s12+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s9+
         s18->s10+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s17+
         s19->s3+
         s19->s8+
         s19->s9+
         s19->s10+
         s19->s12+
         s19->s14+
         s19->s16+
         s20->s1+
         s20->s2+
         s20->s4+
         s20->s8+
         s20->s14+
         s20->s17+
         s20->s18+
         s21->s3+
         s21->s5+
         s21->s6+
         s21->s8+
         s21->s10+
         s21->s13+
         s21->s15+
         s21->s17+
         s21->s20+
         s22->s4+
         s22->s6+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s11+
         s22->s12+
         s22->s14+
         s22->s20+
         s23->s2+
         s23->s5+
         s23->s7+
         s23->s9+
         s23->s10+
         s23->s11+
         s23->s13+
         s23->s15+
         s23->s17+
         s23->s18+
         s23->s20+
         s23->s21+
         s24->s1+
         s24->s3+
         s24->s6+
         s24->s7+
         s24->s8+
         s24->s10+
         s24->s14+
         s24->s15+
         s24->s17+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s0+
         s25->s1+
         s25->s3+
         s25->s5+
         s25->s6+
         s25->s8+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s17+
         s25->s18+
         s25->s20+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s2+
         s26->s4+
         s26->s6+
         s26->s7+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s21+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s1+
         s27->s7+
         s27->s9+
         s27->s13+
         s27->s17+
         s27->s23+
         s27->s25+
         s28->s3+
         s28->s5+
         s28->s12+
         s28->s14+
         s28->s16+
         s28->s17+
         s28->s20+
         s28->s21+
         s28->s25+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s2+
         s29->s6+
         s29->s7+
         s29->s8+
         s29->s12+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s23+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r2+
         r4->r1+
         r4->r2+
         r5->r0+
         r5->r1+
         r6->r1+
         r6->r3+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r4+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r1+
         r10->r2+
         r10->r3+
         r10->r4+
         r10->r8+
         r11->r1+
         r11->r3+
         r11->r5+
         r11->r9+
         r11->r10+
         r12->r0+
         r12->r1+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r7+
         r12->r8+
         r12->r10+
         r13->r0+
         r13->r3+
         r13->r6+
         r13->r8+
         r13->r10+
         r13->r11+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r10+
         r15->r0+
         r15->r2+
         r15->r4+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r11+
         r15->r12+
         r16->r1+
         r16->r2+
         r16->r3+
         r16->r5+
         r16->r8+
         r16->r9+
         r16->r10+
         r16->r12+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r11+
         r17->r13+
         r17->r14+
         r17->r16+
         r18->r2+
         r18->r3+
         r18->r4+
         r18->r8+
         r18->r9+
         r18->r12+
         r18->r14+
         r18->r15+
         r18->r17+
         r19->r1+
         r19->r5+
         r19->r8+
         r19->r13+
         r19->r14+
         r19->r15+
         r19->r16+
         r19->r17+
         r19->r18+
         r20->r1+
         r20->r3+
         r20->r4+
         r20->r5+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r11+
         r20->r15+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r2+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r11+
         r21->r13+
         r21->r14+
         r21->r15+
         r21->r16+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r5+
         r22->r8+
         r22->r9+
         r22->r17+
         r22->r20+
         r23->r1+
         r23->r6+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r12+
         r23->r16+
         r23->r19+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r3+
         r24->r5+
         r24->r8+
         r24->r9+
         r24->r12+
         r24->r13+
         r24->r16+
         r24->r19+
         r24->r21+
         r24->r22+
         r25->r0+
         r25->r2+
         r25->r4+
         r25->r6+
         r25->r7+
         r25->r10+
         r25->r11+
         r25->r13+
         r25->r15+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r24+
         r26->r1+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r10+
         r26->r11+
         r26->r13+
         r26->r15+
         r26->r17+
         r26->r19+
         r26->r20+
         r27->r1+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r21+
         r27->r22+
         r27->r23+
         r27->r24+
         r27->r26+
         r28->r0+
         r28->r1+
         r28->r5+
         r28->r7+
         r28->r8+
         r28->r9+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r17+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r25+
         r28->r26+
         r29->r4+
         r29->r9+
         r29->r11+
         r29->r12+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r17+
         r29->r18+
         r29->r21+
         r29->r24+
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
    s =s10
    t =r22
    m = permission
    p = 2
    c = c4+c2+c7+c8+c9+c5
}
one sig rule1 extends Rule{}{
    s =s26
    t =r10
    m = permission
    p = 2
    c = c1+c0
}
one sig rule2 extends Rule{}{
    s =s7
    t =r12
    m = permission
    p = 0
    c = c7+c6+c1+c9+c4+c2+c3
}
one sig rule3 extends Rule{}{
    s =s25
    t =r13
    m = permission
    p = 4
    c = c1+c4+c3+c9+c7
}
one sig rule4 extends Rule{}{
    s =s1
    t =r15
    m = permission
    p = 1
    c = c7
}
one sig rule5 extends Rule{}{
    s =s20
    t =r26
    m = prohibition
    p = 3
    c = c0+c9+c5+c1+c7+c3+c2
}
one sig rule6 extends Rule{}{
    s =s25
    t =r27
    m = permission
    p = 2
    c = c4+c8+c7+c1+c9+c2
}
one sig rule7 extends Rule{}{
    s =s9
    t =r2
    m = prohibition
    p = 2
    c = c6+c4+c1+c8+c3+c5
}
one sig rule8 extends Rule{}{
    s =s28
    t =r12
    m = permission
    p = 3
    c = c2+c5+c3+c0+c4
}
one sig rule9 extends Rule{}{
    s =s20
    t =r7
    m = prohibition
    p = 0
    c = c2+c1+c6+c8+c3+c4
}
one sig rule10 extends Rule{}{
    s =s2
    t =r29
    m = permission
    p = 3
    c = c0+c4+c1+c7+c5+c2
}
one sig rule11 extends Rule{}{
    s =s4
    t =r21
    m = prohibition
    p = 1
    c = c5+c8+c2+c7+c9+c4
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
