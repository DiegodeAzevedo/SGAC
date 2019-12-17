module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s3->s0+
         s3->s2+
         s4->s1+
         s5->s0+
         s5->s2+
         s5->s3+
         s6->s0+
         s6->s1+
         s6->s5+
         s7->s1+
         s7->s2+
         s7->s3+
         s7->s6+
         s8->s0+
         s8->s3+
         s8->s7+
         s9->s0+
         s9->s1+
         s9->s2+
         s9->s3+
         s9->s5+
         s9->s7+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s3+
         s10->s4+
         s10->s5+
         s10->s6+
         s11->s3+
         s11->s4+
         s11->s5+
         s11->s6+
         s11->s7+
         s11->s8+
         s11->s10+
         s12->s0+
         s12->s4+
         s12->s5+
         s12->s7+
         s12->s9+
         s12->s11+
         s13->s0+
         s13->s2+
         s13->s3+
         s13->s6+
         s13->s7+
         s13->s8+
         s13->s9+
         s14->s0+
         s14->s3+
         s14->s5+
         s14->s6+
         s14->s8+
         s14->s9+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s6+
         s15->s9+
         s15->s10+
         s15->s12+
         s15->s13+
         s16->s1+
         s16->s2+
         s16->s3+
         s16->s4+
         s16->s10+
         s16->s12+
         s16->s15+
         s17->s0+
         s17->s2+
         s17->s3+
         s17->s4+
         s17->s5+
         s17->s6+
         s17->s7+
         s17->s12+
         s17->s15+
         s18->s4+
         s18->s8+
         s18->s10+
         s18->s11+
         s18->s13+
         s19->s1+
         s19->s3+
         s19->s5+
         s19->s6+
         s19->s8+
         s19->s9+
         s19->s12+
         s19->s14+
         s19->s17+
         s20->s0+
         s20->s1+
         s20->s4+
         s20->s6+
         s20->s7+
         s20->s8+
         s20->s9+
         s20->s10+
         s20->s12+
         s20->s15+
         s20->s16+
         s20->s18+
         s21->s1+
         s21->s2+
         s21->s6+
         s21->s8+
         s21->s9+
         s21->s11+
         s21->s13+
         s21->s14+
         s21->s15+
         s21->s16+
         s21->s18+
         s22->s4+
         s22->s5+
         s22->s6+
         s22->s8+
         s22->s9+
         s22->s16+
         s22->s18+
         s22->s20+
         s23->s0+
         s23->s1+
         s23->s2+
         s23->s3+
         s23->s4+
         s23->s5+
         s23->s6+
         s23->s7+
         s23->s8+
         s23->s9+
         s23->s11+
         s23->s12+
         s23->s13+
         s23->s17+
         s23->s19+
         s23->s22+
         s24->s0+
         s24->s4+
         s24->s5+
         s24->s8+
         s24->s10+
         s24->s11+
         s24->s13+
         s24->s14+
         s24->s15+
         s24->s16+
         s24->s21+
         s24->s22+
         s24->s23+
         s25->s4+
         s25->s7+
         s25->s9+
         s25->s11+
         s25->s14+
         s26->s2+
         s26->s5+
         s26->s6+
         s26->s7+
         s26->s9+
         s26->s10+
         s26->s23+
         s27->s1+
         s27->s2+
         s27->s4+
         s27->s8+
         s27->s10+
         s27->s12+
         s27->s13+
         s27->s15+
         s27->s16+
         s27->s17+
         s27->s20+
         s28->s1+
         s28->s3+
         s28->s6+
         s28->s7+
         s28->s8+
         s28->s12+
         s28->s13+
         s28->s14+
         s28->s15+
         s28->s16+
         s28->s17+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s26+
         s28->s27+
         s29->s0+
         s29->s1+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s9+
         s29->s10+
         s29->s13+
         s29->s14+
         s29->s15+
         s29->s17+
         s29->s18+
         s29->s19+
         s29->s21+
         s29->s22+
         s29->s24+
         s29->s26+
         s29->s28}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r4->r0+
         r4->r3+
         r5->r1+
         r5->r4+
         r6->r0+
         r6->r2+
         r6->r3+
         r7->r1+
         r7->r2+
         r7->r3+
         r7->r4+
         r7->r5+
         r8->r2+
         r9->r8+
         r10->r0+
         r10->r2+
         r10->r6+
         r11->r2+
         r11->r4+
         r11->r6+
         r11->r9+
         r11->r10+
         r12->r6+
         r12->r8+
         r12->r9+
         r12->r10+
         r13->r3+
         r13->r4+
         r13->r5+
         r13->r6+
         r13->r8+
         r13->r9+
         r13->r10+
         r13->r12+
         r14->r0+
         r14->r8+
         r14->r9+
         r14->r10+
         r14->r12+
         r14->r13+
         r15->r1+
         r15->r2+
         r15->r3+
         r15->r4+
         r15->r5+
         r15->r10+
         r15->r11+
         r16->r0+
         r16->r3+
         r16->r4+
         r16->r5+
         r16->r9+
         r16->r10+
         r16->r11+
         r16->r12+
         r16->r15+
         r17->r0+
         r17->r1+
         r17->r2+
         r17->r3+
         r17->r4+
         r17->r5+
         r17->r7+
         r17->r9+
         r17->r10+
         r17->r11+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r1+
         r18->r5+
         r18->r7+
         r18->r9+
         r18->r10+
         r18->r13+
         r18->r16+
         r19->r0+
         r19->r1+
         r19->r3+
         r19->r4+
         r19->r7+
         r19->r15+
         r19->r16+
         r20->r0+
         r20->r2+
         r20->r3+
         r20->r5+
         r20->r6+
         r20->r11+
         r20->r14+
         r20->r15+
         r20->r18+
         r21->r0+
         r21->r1+
         r21->r3+
         r21->r5+
         r21->r9+
         r21->r11+
         r21->r12+
         r21->r13+
         r21->r14+
         r21->r17+
         r22->r0+
         r22->r1+
         r22->r2+
         r22->r3+
         r22->r6+
         r22->r7+
         r22->r11+
         r22->r12+
         r22->r14+
         r22->r17+
         r22->r18+
         r22->r19+
         r22->r20+
         r22->r21+
         r23->r2+
         r23->r4+
         r23->r7+
         r23->r8+
         r23->r10+
         r23->r13+
         r23->r14+
         r23->r19+
         r24->r2+
         r24->r3+
         r24->r4+
         r24->r7+
         r24->r13+
         r24->r14+
         r24->r15+
         r24->r17+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r2+
         r25->r4+
         r25->r5+
         r25->r6+
         r25->r7+
         r25->r11+
         r25->r16+
         r25->r19+
         r25->r20+
         r25->r21+
         r25->r22+
         r26->r3+
         r26->r4+
         r26->r6+
         r26->r8+
         r26->r10+
         r26->r11+
         r26->r12+
         r26->r13+
         r26->r19+
         r26->r22+
         r26->r23+
         r27->r2+
         r27->r4+
         r27->r6+
         r27->r8+
         r27->r9+
         r27->r11+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r16+
         r27->r18+
         r27->r19+
         r27->r20+
         r27->r22+
         r27->r23+
         r27->r25+
         r28->r0+
         r28->r1+
         r28->r3+
         r28->r4+
         r28->r6+
         r28->r7+
         r28->r8+
         r28->r12+
         r28->r17+
         r28->r19+
         r28->r21+
         r28->r24+
         r28->r25+
         r29->r1+
         r29->r2+
         r29->r4+
         r29->r6+
         r29->r8+
         r29->r10+
         r29->r11+
         r29->r13+
         r29->r14+
         r29->r15+
         r29->r16+
         r29->r17+
         r29->r19+
         r29->r24+
         r29->r25+
         r29->r27}

//*************************
//***Contexts signatures***
//*************************
one sig c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 extends Context{}{}

//************************
//***Request signatures***
//************************
one sig req3 extends Request{}{
sub=s2
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s27
    t =r10
    m = prohibition
    p = 0
    c = c8+c9
}
one sig rule1 extends Rule{}{
    s =s4
    t =r16
    m = prohibition
    p = 2
    c = c4+c7+c6
}
one sig rule2 extends Rule{}{
    s =s5
    t =r0
    m = prohibition
    p = 3
    c = c9+c7+c0+c3+c2
}
one sig rule3 extends Rule{}{
    s =s8
    t =r19
    m = permission
    p = 2
    c = c1+c4
}
one sig rule4 extends Rule{}{
    s =s29
    t =r15
    m = prohibition
    p = 4
    c = c0
}
one sig rule5 extends Rule{}{
    s =s7
    t =r29
    m = permission
    p = 0
    c = c8+c5+c6
}
one sig rule6 extends Rule{}{
    s =s24
    t =r23
    m = permission
    p = 4
    c = c1+c9
}
one sig rule7 extends Rule{}{
    s =s27
    t =r0
    m = prohibition
    p = 0
    c = c8+c7
}
one sig rule8 extends Rule{}{
    s =s19
    t =r16
    m = permission
    p = 4
    c = c2+c1+c9+c6+c8
}
one sig rule9 extends Rule{}{
    s =s25
    t =r17
    m = prohibition
    p = 4
    c = c8+c7+c3
}
one sig rule10 extends Rule{}{
    s =s11
    t =r27
    m = permission
    p = 2
    c = c5+c4+c7+c3+c6+c0
}
one sig rule11 extends Rule{}{
    s =s21
    t =r18
    m = prohibition
    p = 1
    c = c6+c4
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
