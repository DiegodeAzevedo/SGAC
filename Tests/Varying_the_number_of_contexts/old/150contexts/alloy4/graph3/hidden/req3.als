module filepath/param/graph/property/req
open filepath/alloy4/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s3+
         s7->s0+
         s7->s1+
         s7->s2+
         s7->s6+
         s8->s4+
         s8->s5+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s4+
         s10->s6+
         s10->s7+
         s10->s8+
         s11->s4+
         s11->s6+
         s11->s10+
         s12->s0+
         s12->s2+
         s12->s3+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s1+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s7+
         s13->s8+
         s14->s2+
         s14->s5+
         s14->s11+
         s14->s13+
         s15->s0+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s9+
         s15->s10+
         s15->s11+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s1+
         s16->s3+
         s16->s4+
         s16->s9+
         s16->s10+
         s16->s13+
         s16->s15+
         s17->s2+
         s17->s5+
         s17->s7+
         s17->s10+
         s17->s11+
         s17->s12+
         s17->s16+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s10+
         s18->s17+
         s19->s6+
         s19->s8+
         s19->s10+
         s19->s12+
         s19->s15+
         s19->s17+
         s20->s2+
         s20->s3+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s11+
         s20->s12+
         s20->s13+
         s20->s15+
         s20->s16+
         s20->s17+
         s21->s3+
         s21->s7+
         s21->s9+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s17+
         s21->s20+
         s22->s0+
         s22->s2+
         s22->s3+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s11+
         s22->s12+
         s22->s13+
         s22->s15+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s2+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s10+
         s23->s11+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s18+
         s23->s19+
         s23->s20+
         s23->s21+
         s23->s22+
         s24->s1+
         s24->s4+
         s24->s5+
         s24->s6+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s16+
         s24->s18+
         s24->s20+
         s24->s22+
         s24->s23+
         s25->s1+
         s25->s6+
         s25->s10+
         s25->s12+
         s25->s13+
         s25->s15+
         s25->s16+
         s25->s18+
         s25->s19+
         s25->s20+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s9+
         s26->s11+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s22+
         s26->s23+
         s26->s24+
         s27->s1+
         s27->s2+
         s27->s3+
         s27->s6+
         s27->s11+
         s27->s12+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s19+
         s27->s20+
         s27->s22+
         s27->s23+
         s28->s3+
         s28->s4+
         s28->s8+
         s28->s9+
         s28->s12+
         s28->s13+
         s28->s15+
         s28->s16+
         s28->s18+
         s28->s22+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s1+
         s29->s3+
         s29->s4+
         s29->s5+
         s29->s8+
         s29->s11+
         s29->s14+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s21+
         s29->s23+
         s29->s24+
         s29->s25+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r0+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r4+
         r7->r0+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r6+
         r8->r0+
         r8->r1+
         r8->r2+
         r8->r3+
         r8->r4+
         r8->r6+
         r8->r7+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r8+
         r10->r0+
         r10->r1+
         r10->r4+
         r10->r6+
         r10->r7+
         r11->r5+
         r11->r8+
         r11->r9+
         r12->r2+
         r12->r4+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r12->r11+
         r13->r0+
         r13->r4+
         r13->r8+
         r13->r9+
         r14->r0+
         r14->r2+
         r14->r4+
         r14->r5+
         r14->r6+
         r14->r8+
         r14->r10+
         r14->r11+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r8+
         r15->r10+
         r16->r0+
         r16->r2+
         r16->r4+
         r16->r5+
         r16->r6+
         r16->r8+
         r16->r11+
         r16->r13+
         r16->r15+
         r17->r0+
         r17->r2+
         r17->r3+
         r17->r5+
         r17->r6+
         r17->r7+
         r17->r8+
         r17->r9+
         r17->r10+
         r17->r14+
         r17->r16+
         r18->r2+
         r18->r4+
         r18->r5+
         r18->r7+
         r18->r8+
         r18->r11+
         r18->r12+
         r18->r14+
         r18->r15+
         r19->r2+
         r19->r3+
         r19->r8+
         r19->r9+
         r19->r10+
         r19->r11+
         r19->r17+
         r19->r18+
         r20->r0+
         r20->r3+
         r20->r4+
         r20->r6+
         r20->r12+
         r20->r14+
         r20->r16+
         r20->r19+
         r21->r1+
         r21->r4+
         r21->r5+
         r21->r6+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r12+
         r21->r13+
         r21->r15+
         r21->r17+
         r21->r18+
         r22->r1+
         r22->r3+
         r22->r5+
         r22->r6+
         r22->r8+
         r22->r9+
         r22->r10+
         r22->r12+
         r22->r13+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r21+
         r23->r2+
         r23->r5+
         r23->r8+
         r23->r9+
         r23->r10+
         r23->r11+
         r23->r15+
         r23->r16+
         r23->r18+
         r23->r21+
         r24->r3+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r8+
         r24->r10+
         r24->r12+
         r24->r13+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r21+
         r24->r22+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r9+
         r25->r10+
         r25->r13+
         r25->r14+
         r25->r15+
         r25->r18+
         r25->r19+
         r25->r22+
         r26->r1+
         r26->r10+
         r26->r15+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r22+
         r26->r25+
         r27->r0+
         r27->r3+
         r27->r7+
         r27->r10+
         r27->r12+
         r27->r15+
         r27->r16+
         r27->r17+
         r27->r18+
         r27->r23+
         r27->r24+
         r28->r0+
         r28->r2+
         r28->r4+
         r28->r5+
         r28->r6+
         r28->r9+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r27+
         r29->r0+
         r29->r3+
         r29->r4+
         r29->r5+
         r29->r7+
         r29->r10+
         r29->r12+
         r29->r13+
         r29->r19+
         r29->r21+
         r29->r22+
         r29->r24}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s2
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s26
    t =r26
    m = prohibition
    p = 3
    c = c7+c1+c4+c5+c6+c0
}
one sig rule1 extends Rule{}{
    s =s27
    t =r28
    m = prohibition
    p = 1
    c = c3+c6+c1+c7+c2+c5
}
one sig rule2 extends Rule{}{
    s =s19
    t =r4
    m = permission
    p = 3
    c = c6+c1+c3+c4+c5+c0
}
one sig rule3 extends Rule{}{
    s =s22
    t =r22
    m = prohibition
    p = 3
    c = c7+c5+c3+c9+c6
}
one sig rule4 extends Rule{}{
    s =s1
    t =r15
    m = permission
    p = 1
    c = c9+c1+c2+c6+c3+c0+c5+c8
}
one sig rule5 extends Rule{}{
    s =s20
    t =r26
    m = prohibition
    p = 0
    c = c7+c8+c2+c3+c4
}
one sig rule6 extends Rule{}{
    s =s5
    t =r1
    m = prohibition
    p = 1
    c = c1+c2+c4+c7+c6
}
one sig rule7 extends Rule{}{
    s =s9
    t =r16
    m = permission
    p = 2
    c = c3+c8+c0+c5+c4
}
one sig rule8 extends Rule{}{
    s =s23
    t =r28
    m = prohibition
    p = 2
    c = c3+c9+c1+c7+c5
}
one sig rule9 extends Rule{}{
    s =s22
    t =r23
    m = prohibition
    p = 2
    c = c0+c3+c9+c6+c8+c2
}
one sig rule10 extends Rule{}{
    s =s18
    t =r26
    m = prohibition
    p = 1
    c = c3+c4+c8+c6
}
one sig rule11 extends Rule{}{
    s =s19
    t =r25
    m = permission
    p = 2
    c = c2+c7+c5+c4+c6+c1
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
