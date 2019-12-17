module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s0+
         s2->s1+
         s3->s1+
         s3->s2+
         s4->s3+
         s5->s1+
         s6->s0+
         s6->s3+
         s6->s4+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s4+
         s7->s5+
         s8->s0+
         s8->s2+
         s8->s4+
         s8->s7+
         s9->s0+
         s9->s3+
         s9->s4+
         s9->s8+
         s10->s3+
         s10->s5+
         s11->s0+
         s11->s1+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s9+
         s12->s3+
         s12->s4+
         s12->s6+
         s12->s8+
         s12->s11+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s5+
         s13->s7+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s6+
         s14->s7+
         s14->s11+
         s14->s12+
         s14->s13+
         s15->s4+
         s15->s7+
         s15->s8+
         s15->s11+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s7+
         s16->s8+
         s16->s10+
         s16->s12+
         s16->s13+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s4+
         s17->s6+
         s17->s7+
         s17->s9+
         s17->s13+
         s17->s14+
         s17->s15+
         s17->s16+
         s18->s0+
         s18->s3+
         s18->s4+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s10+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s18->s16+
         s19->s0+
         s19->s3+
         s19->s6+
         s19->s7+
         s19->s11+
         s19->s12+
         s19->s13+
         s19->s14+
         s19->s16+
         s20->s0+
         s20->s1+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s7+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s14+
         s20->s16+
         s20->s19+
         s21->s1+
         s21->s3+
         s21->s4+
         s21->s5+
         s21->s7+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s17+
         s21->s18+
         s21->s19+
         s21->s20+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s10+
         s22->s11+
         s22->s13+
         s22->s14+
         s22->s16+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s1+
         s23->s5+
         s23->s9+
         s23->s11+
         s23->s13+
         s23->s14+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s21+
         s24->s1+
         s24->s4+
         s24->s6+
         s24->s8+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s16+
         s24->s17+
         s24->s18+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s8+
         s25->s10+
         s25->s11+
         s25->s12+
         s25->s13+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s19+
         s25->s21+
         s25->s23+
         s26->s2+
         s26->s4+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s11+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s24+
         s27->s3+
         s27->s4+
         s27->s6+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s18+
         s27->s21+
         s27->s23+
         s27->s24+
         s27->s25+
         s28->s4+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s9+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s17+
         s28->s18+
         s28->s21+
         s28->s22+
         s28->s27+
         s29->s2+
         s29->s6+
         s29->s10+
         s29->s11+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s20+
         s29->s22+
         s29->s23+
         s29->s25+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r3->r0+
         r4->r2+
         r5->r0+
         r5->r1+
         r5->r2+
         r5->r3+
         r6->r0+
         r6->r3+
         r7->r0+
         r7->r3+
         r8->r0+
         r8->r1+
         r8->r7+
         r9->r0+
         r9->r2+
         r9->r3+
         r9->r7+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r5+
         r10->r7+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r6+
         r12->r5+
         r12->r9+
         r13->r0+
         r13->r2+
         r13->r3+
         r13->r8+
         r13->r9+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r4+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r3+
         r15->r4+
         r15->r8+
         r15->r11+
         r16->r5+
         r16->r9+
         r16->r12+
         r17->r1+
         r17->r3+
         r17->r6+
         r17->r10+
         r17->r11+
         r17->r12+
         r17->r13+
         r17->r15+
         r18->r0+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r15+
         r18->r16+
         r19->r1+
         r19->r2+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r15+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r3+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r9+
         r20->r10+
         r20->r12+
         r20->r13+
         r20->r14+
         r20->r16+
         r20->r17+
         r20->r18+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r6+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r16+
         r21->r20+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r6+
         r22->r7+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r15+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r0+
         r23->r3+
         r23->r4+
         r23->r6+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r14+
         r23->r15+
         r23->r16+
         r23->r17+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r1+
         r24->r2+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r8+
         r24->r11+
         r24->r12+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r19+
         r24->r20+
         r25->r0+
         r25->r1+
         r25->r5+
         r25->r6+
         r25->r8+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r15+
         r25->r18+
         r25->r19+
         r25->r22+
         r25->r24+
         r26->r0+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r15+
         r26->r16+
         r26->r18+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r27->r0+
         r27->r1+
         r27->r5+
         r27->r8+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r15+
         r27->r17+
         r27->r22+
         r27->r25+
         r28->r1+
         r28->r5+
         r28->r6+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r14+
         r28->r15+
         r28->r19+
         r28->r21+
         r28->r25+
         r28->r26+
         r29->r2+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r7+
         r29->r11+
         r29->r12+
         r29->r14+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r22+
         r29->r27+
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
    s =s25
    t =r4
    m = permission
    p = 1
    c = c4+c1+c8+c9+c2
}
one sig rule1 extends Rule{}{
    s =s10
    t =r28
    m = permission
    p = 1
    c = c1+c0+c3+c7+c2
}
one sig rule2 extends Rule{}{
    s =s12
    t =r14
    m = permission
    p = 3
    c = c9+c6+c1
}
one sig rule3 extends Rule{}{
    s =s19
    t =r2
    m = prohibition
    p = 0
    c = c5+c7+c3+c1
}
one sig rule4 extends Rule{}{
    s =s16
    t =r5
    m = prohibition
    p = 2
    c = c9
}
one sig rule5 extends Rule{}{
    s =s27
    t =r9
    m = prohibition
    p = 2
    c = c2+c7+c9+c4
}
one sig rule6 extends Rule{}{
    s =s24
    t =r16
    m = permission
    p = 3
    c = c4+c2+c1+c3
}
one sig rule7 extends Rule{}{
    s =s7
    t =r1
    m = permission
    p = 4
    c = c3+c4+c0+c8+c2+c9
}
one sig rule8 extends Rule{}{
    s =s16
    t =r1
    m = permission
    p = 2
    c = c2+c5
}
one sig rule9 extends Rule{}{
    s =s23
    t =r23
    m = prohibition
    p = 2
    c = c0+c5+c6
}
one sig rule10 extends Rule{}{
    s =s22
    t =r28
    m = prohibition
    p = 3
    c = c5+c3+c1+c2+c6
}
one sig rule11 extends Rule{}{
    s =s18
    t =r15
    m = prohibition
    p = 4
    c = c0+c8+c9+c3
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
