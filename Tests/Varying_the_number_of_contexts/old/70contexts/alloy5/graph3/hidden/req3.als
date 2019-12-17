module filepath/param/graph/property/req
open filepath/alloy5/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s3->s0+
         s3->s2+
         s4->s1+
         s4->s2+
         s4->s3+
         s5->s0+
         s6->s0+
         s6->s2+
         s6->s3+
         s7->s0+
         s7->s2+
         s7->s3+
         s7->s4+
         s8->s2+
         s8->s6+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s4+
         s9->s5+
         s10->s1+
         s10->s5+
         s10->s6+
         s10->s7+
         s11->s0+
         s11->s3+
         s11->s4+
         s11->s7+
         s11->s9+
         s11->s10+
         s12->s1+
         s12->s2+
         s12->s3+
         s12->s7+
         s12->s8+
         s12->s11+
         s13->s2+
         s13->s3+
         s13->s4+
         s13->s5+
         s13->s6+
         s13->s9+
         s13->s10+
         s13->s11+
         s13->s12+
         s14->s1+
         s14->s2+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s6+
         s14->s7+
         s14->s8+
         s14->s10+
         s14->s11+
         s15->s3+
         s15->s4+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s12+
         s15->s13+
         s15->s14+
         s16->s0+
         s16->s1+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s8+
         s16->s9+
         s16->s10+
         s16->s14+
         s16->s15+
         s17->s2+
         s17->s4+
         s17->s5+
         s17->s8+
         s17->s9+
         s17->s12+
         s17->s13+
         s17->s15+
         s18->s0+
         s18->s2+
         s18->s3+
         s18->s6+
         s18->s7+
         s18->s8+
         s18->s9+
         s18->s11+
         s18->s12+
         s18->s13+
         s18->s14+
         s18->s16+
         s18->s17+
         s19->s0+
         s19->s3+
         s19->s5+
         s19->s8+
         s19->s16+
         s20->s3+
         s20->s6+
         s20->s10+
         s20->s11+
         s20->s14+
         s21->s0+
         s21->s2+
         s21->s5+
         s21->s6+
         s21->s7+
         s21->s8+
         s21->s10+
         s21->s11+
         s21->s13+
         s21->s15+
         s21->s16+
         s21->s17+
         s22->s1+
         s22->s2+
         s22->s3+
         s22->s4+
         s22->s5+
         s22->s7+
         s22->s8+
         s22->s9+
         s22->s10+
         s22->s12+
         s22->s13+
         s22->s18+
         s22->s19+
         s22->s20+
         s23->s0+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s9+
         s23->s14+
         s23->s15+
         s23->s16+
         s23->s17+
         s23->s19+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s10+
         s24->s12+
         s24->s13+
         s24->s15+
         s24->s18+
         s24->s19+
         s24->s21+
         s24->s22+
         s25->s2+
         s25->s4+
         s25->s8+
         s25->s10+
         s25->s16+
         s25->s19+
         s25->s23+
         s26->s0+
         s26->s3+
         s26->s6+
         s26->s8+
         s26->s12+
         s26->s13+
         s26->s14+
         s26->s15+
         s26->s17+
         s26->s18+
         s26->s20+
         s26->s22+
         s26->s25+
         s27->s3+
         s27->s4+
         s27->s5+
         s27->s8+
         s27->s12+
         s27->s13+
         s27->s14+
         s27->s15+
         s27->s16+
         s27->s18+
         s27->s20+
         s27->s21+
         s28->s2+
         s28->s4+
         s28->s6+
         s28->s8+
         s28->s11+
         s28->s12+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s19+
         s28->s20+
         s28->s27+
         s29->s1+
         s29->s2+
         s29->s3+
         s29->s6+
         s29->s8+
         s29->s9+
         s29->s11+
         s29->s12+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s23+
         s29->s26+
         s29->s27+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r1+
         r3->r1+
         r4->r1+
         r4->r2+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r6+
         r8->r2+
         r8->r5+
         r9->r0+
         r9->r1+
         r9->r2+
         r9->r3+
         r9->r4+
         r9->r6+
         r9->r8+
         r10->r1+
         r10->r3+
         r10->r4+
         r10->r6+
         r10->r7+
         r11->r0+
         r11->r3+
         r11->r4+
         r11->r7+
         r11->r8+
         r11->r9+
         r12->r0+
         r12->r2+
         r12->r3+
         r12->r4+
         r12->r9+
         r13->r1+
         r13->r2+
         r13->r3+
         r13->r8+
         r13->r9+
         r13->r11+
         r13->r12+
         r14->r1+
         r14->r2+
         r14->r3+
         r14->r6+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r1+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r7+
         r15->r10+
         r15->r12+
         r15->r13+
         r16->r1+
         r16->r5+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r10+
         r16->r14+
         r16->r15+
         r17->r1+
         r17->r3+
         r17->r6+
         r17->r7+
         r17->r12+
         r17->r13+
         r17->r15+
         r17->r16+
         r18->r0+
         r18->r2+
         r18->r4+
         r18->r7+
         r18->r8+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r14+
         r18->r15+
         r18->r16+
         r18->r17+
         r19->r1+
         r19->r2+
         r19->r4+
         r19->r5+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r18+
         r20->r0+
         r20->r1+
         r20->r2+
         r20->r4+
         r20->r6+
         r20->r7+
         r20->r8+
         r20->r11+
         r20->r14+
         r20->r16+
         r20->r17+
         r20->r18+
         r21->r0+
         r21->r2+
         r21->r3+
         r21->r5+
         r21->r9+
         r21->r12+
         r21->r13+
         r21->r17+
         r22->r0+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r8+
         r22->r13+
         r22->r15+
         r22->r16+
         r22->r17+
         r22->r18+
         r22->r20+
         r23->r0+
         r23->r1+
         r23->r3+
         r23->r4+
         r23->r5+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r16+
         r23->r19+
         r23->r21+
         r23->r22+
         r24->r0+
         r24->r2+
         r24->r4+
         r24->r5+
         r24->r6+
         r24->r7+
         r24->r13+
         r24->r14+
         r24->r18+
         r24->r20+
         r24->r21+
         r25->r1+
         r25->r4+
         r25->r7+
         r25->r9+
         r25->r10+
         r25->r11+
         r25->r12+
         r25->r14+
         r25->r15+
         r25->r16+
         r25->r17+
         r25->r18+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r2+
         r26->r5+
         r26->r6+
         r26->r7+
         r26->r8+
         r26->r9+
         r26->r10+
         r26->r13+
         r26->r15+
         r26->r19+
         r26->r21+
         r26->r24+
         r26->r25+
         r27->r3+
         r27->r4+
         r27->r8+
         r27->r10+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r19+
         r27->r23+
         r27->r26+
         r28->r4+
         r28->r7+
         r28->r9+
         r28->r11+
         r28->r12+
         r28->r13+
         r28->r14+
         r28->r17+
         r28->r18+
         r28->r19+
         r28->r22+
         r28->r26+
         r28->r27+
         r29->r2+
         r29->r4+
         r29->r5+
         r29->r8+
         r29->r10+
         r29->r14+
         r29->r17+
         r29->r20+
         r29->r21+
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
sub=s1
res=r1
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s27
    t =r21
    m = prohibition
    p = 4
    c = c9+c2+c7
}
one sig rule1 extends Rule{}{
    s =s21
    t =r16
    m = permission
    p = 2
    c = c9+c3+c0+c8
}
one sig rule2 extends Rule{}{
    s =s14
    t =r16
    m = prohibition
    p = 0
    c = c3+c1+c9+c2
}
one sig rule3 extends Rule{}{
    s =s28
    t =r2
    m = permission
    p = 0
    c = c1+c5+c4+c6+c7+c2
}
one sig rule4 extends Rule{}{
    s =s7
    t =r19
    m = prohibition
    p = 2
    c = c8+c5+c7+c0+c1+c2
}
one sig rule5 extends Rule{}{
    s =s1
    t =r8
    m = permission
    p = 0
    c = c3
}
one sig rule6 extends Rule{}{
    s =s17
    t =r27
    m = permission
    p = 4
    c = c6+c5+c9+c0+c2+c8+c3+c7
}
one sig rule7 extends Rule{}{
    s =s3
    t =r15
    m = prohibition
    p = 3
    c = c7+c4+c1
}
one sig rule8 extends Rule{}{
    s =s24
    t =r7
    m = permission
    p = 2
    c = c9+c8+c6
}
one sig rule9 extends Rule{}{
    s =s27
    t =r2
    m = permission
    p = 0
    c = c2+c0
}
one sig rule10 extends Rule{}{
    s =s17
    t =r19
    m = permission
    p = 1
    c = c2+c0+c8
}
one sig rule11 extends Rule{}{
    s =s27
    t =r0
    m = prohibition
    p = 1
    c = c9+c6+c2+c7+c5+c4+c0+c1+c3
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
