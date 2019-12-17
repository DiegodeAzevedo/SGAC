module filepath/param/graph/property/req
open filepath/alloy1/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s5->s2+
         s5->s4+
         s6->s0+
         s6->s3+
         s7->s0+
         s7->s3+
         s7->s4+
         s8->s0+
         s8->s1+
         s8->s2+
         s8->s6+
         s9->s0+
         s9->s2+
         s9->s7+
         s10->s4+
         s10->s5+
         s10->s7+
         s10->s9+
         s11->s0+
         s11->s2+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s7+
         s11->s8+
         s11->s9+
         s11->s10+
         s12->s4+
         s12->s5+
         s12->s6+
         s12->s7+
         s12->s8+
         s13->s0+
         s13->s1+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s6+
         s13->s11+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s9+
         s14->s13+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s4+
         s15->s9+
         s15->s12+
         s15->s13+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s8+
         s16->s10+
         s16->s11+
         s16->s12+
         s16->s13+
         s17->s0+
         s17->s1+
         s17->s2+
         s17->s4+
         s17->s8+
         s17->s10+
         s17->s12+
         s17->s16+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s6+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s15+
         s19->s0+
         s19->s3+
         s19->s4+
         s19->s9+
         s19->s11+
         s19->s14+
         s19->s15+
         s19->s16+
         s19->s18+
         s20->s0+
         s20->s1+
         s20->s4+
         s20->s5+
         s20->s6+
         s20->s8+
         s20->s9+
         s20->s13+
         s20->s15+
         s21->s1+
         s21->s5+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s13+
         s21->s14+
         s21->s16+
         s22->s0+
         s22->s1+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s10+
         s22->s11+
         s22->s14+
         s22->s15+
         s22->s18+
         s22->s20+
         s22->s21+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s9+
         s23->s11+
         s23->s12+
         s23->s14+
         s23->s15+
         s23->s20+
         s23->s21+
         s24->s2+
         s24->s3+
         s24->s6+
         s24->s7+
         s24->s11+
         s24->s12+
         s24->s15+
         s24->s16+
         s24->s18+
         s24->s21+
         s25->s0+
         s25->s1+
         s25->s2+
         s25->s3+
         s25->s4+
         s25->s5+
         s25->s7+
         s25->s12+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s17+
         s25->s18+
         s25->s22+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s3+
         s26->s4+
         s26->s8+
         s26->s10+
         s26->s11+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s19+
         s26->s20+
         s26->s24+
         s26->s25+
         s27->s0+
         s27->s2+
         s27->s3+
         s27->s5+
         s27->s6+
         s27->s9+
         s27->s10+
         s27->s11+
         s27->s15+
         s27->s18+
         s27->s20+
         s27->s21+
         s27->s25+
         s28->s0+
         s28->s1+
         s28->s2+
         s28->s5+
         s28->s6+
         s28->s7+
         s28->s11+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s16+
         s28->s19+
         s28->s21+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s1+
         s29->s4+
         s29->s5+
         s29->s6+
         s29->s13+
         s29->s14+
         s29->s17+
         s29->s20+
         s29->s22+
         s29->s24+
         s29->s27}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r2+
         r4->r0+
         r4->r1+
         r4->r2+
         r4->r3+
         r5->r0+
         r5->r1+
         r5->r3+
         r5->r4+
         r6->r1+
         r6->r2+
         r6->r3+
         r8->r0+
         r8->r1+
         r8->r4+
         r8->r6+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r7+
         r10->r0+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r7+
         r10->r8+
         r10->r9+
         r11->r0+
         r11->r1+
         r11->r2+
         r11->r3+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r4+
         r12->r6+
         r12->r7+
         r13->r0+
         r13->r1+
         r13->r3+
         r13->r5+
         r13->r6+
         r13->r7+
         r13->r8+
         r13->r11+
         r14->r5+
         r14->r6+
         r14->r7+
         r14->r8+
         r14->r11+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r5+
         r15->r9+
         r15->r10+
         r15->r11+
         r15->r13+
         r16->r0+
         r16->r1+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r13+
         r16->r14+
         r17->r0+
         r17->r1+
         r17->r5+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r4+
         r18->r5+
         r18->r6+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r12+
         r18->r13+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r5+
         r19->r6+
         r19->r7+
         r19->r8+
         r19->r12+
         r19->r16+
         r19->r18+
         r20->r0+
         r20->r6+
         r20->r9+
         r20->r11+
         r20->r13+
         r20->r15+
         r20->r19+
         r21->r0+
         r21->r1+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r10+
         r21->r11+
         r21->r12+
         r21->r16+
         r21->r17+
         r21->r19+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r4+
         r22->r6+
         r22->r9+
         r22->r12+
         r22->r13+
         r22->r14+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r19+
         r23->r1+
         r23->r2+
         r23->r3+
         r23->r5+
         r23->r14+
         r23->r15+
         r23->r17+
         r23->r21+
         r24->r0+
         r24->r3+
         r24->r6+
         r24->r12+
         r24->r14+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r19+
         r24->r21+
         r25->r1+
         r25->r3+
         r25->r6+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r14+
         r25->r16+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r23+
         r25->r24+
         r26->r2+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r9+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r17+
         r26->r19+
         r26->r22+
         r26->r23+
         r26->r24+
         r27->r1+
         r27->r3+
         r27->r5+
         r27->r6+
         r27->r7+
         r27->r10+
         r27->r11+
         r27->r12+
         r27->r16+
         r27->r20+
         r27->r22+
         r27->r23+
         r28->r1+
         r28->r2+
         r28->r3+
         r28->r4+
         r28->r8+
         r28->r9+
         r28->r13+
         r28->r14+
         r28->r17+
         r28->r18+
         r28->r20+
         r28->r23+
         r28->r24+
         r28->r27+
         r29->r0+
         r29->r3+
         r29->r5+
         r29->r6+
         r29->r8+
         r29->r9+
         r29->r13+
         r29->r14+
         r29->r16+
         r29->r19+
         r29->r25+
         r29->r27+
         r29->r28}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req8 extends Request{}{
sub=s2
res=r7
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s18
    t =r17
    m = prohibition
    p = 4
    c = c1+c4+c6+c0+c8
}
one sig rule1 extends Rule{}{
    s =s29
    t =r18
    m = permission
    p = 3
    c = c5+c3+c2+c4
}
one sig rule2 extends Rule{}{
    s =s24
    t =r27
    m = prohibition
    p = 0
    c = c8+c1+c7+c3+c0+c5
}
one sig rule3 extends Rule{}{
    s =s28
    t =r28
    m = prohibition
    p = 1
    c = c7+c8+c2+c4
}
one sig rule4 extends Rule{}{
    s =s17
    t =r2
    m = prohibition
    p = 4
    c = c7+c3+c6
}
one sig rule5 extends Rule{}{
    s =s1
    t =r10
    m = permission
    p = 4
    c = c6
}
one sig rule6 extends Rule{}{
    s =s3
    t =r11
    m = prohibition
    p = 0
    c = c0+c5+c4+c9+c7
}
one sig rule7 extends Rule{}{
    s =s13
    t =r10
    m = prohibition
    p = 4
    c = c4+c8+c0
}
one sig rule8 extends Rule{}{
    s =s3
    t =r12
    m = prohibition
    p = 1
    c = c8+c3+c5+c7+c9+c1
}
one sig rule9 extends Rule{}{
    s =s17
    t =r1
    m = permission
    p = 2
    c = c9+c8+c4+c5+c6+c2
}
one sig rule10 extends Rule{}{
    s =s21
    t =r9
    m = prohibition
    p = 2
    c = c9+c5+c6+c3+c1+c7
}
one sig rule11 extends Rule{}{
    s =s19
    t =r25
    m = prohibition
    p = 0
    c = c4+c3+c2+c9+c1+c5+c6
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
check HiddenDocument_r7_c0{ HiddenDocument[r7,c0]} for 4
check HiddenDocument_r7_c1{ HiddenDocument[r7,c1]} for 4
check HiddenDocument_r7_c2{ HiddenDocument[r7,c2]} for 4
check HiddenDocument_r7_c3{ HiddenDocument[r7,c3]} for 4
check HiddenDocument_r7_c4{ HiddenDocument[r7,c4]} for 4
check HiddenDocument_r7_c5{ HiddenDocument[r7,c5]} for 4
check HiddenDocument_r7_c6{ HiddenDocument[r7,c6]} for 4
check HiddenDocument_r7_c7{ HiddenDocument[r7,c7]} for 4
check HiddenDocument_r7_c8{ HiddenDocument[r7,c8]} for 4
check HiddenDocument_r7_c9{ HiddenDocument[r7,c9]} for 4
