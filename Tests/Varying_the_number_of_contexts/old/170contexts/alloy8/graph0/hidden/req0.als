module filepath/param/graph/property/req
open filepath/alloy8/sgac_core
//**********************
//***Graph signatures***
//**********************
one sig s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29 extends Subject{}{}
fact{
subSucc=s1->s0+
         s2->s1+
         s3->s0+
         s3->s2+
         s4->s0+
         s4->s1+
         s4->s2+
         s5->s0+
         s5->s1+
         s5->s2+
         s5->s3+
         s5->s4+
         s6->s0+
         s6->s1+
         s6->s2+
         s6->s4+
         s7->s3+
         s7->s4+
         s7->s6+
         s8->s1+
         s8->s5+
         s8->s6+
         s8->s7+
         s9->s2+
         s9->s3+
         s9->s8+
         s10->s0+
         s10->s1+
         s10->s2+
         s10->s3+
         s10->s5+
         s10->s6+
         s10->s7+
         s10->s8+
         s10->s9+
         s11->s3+
         s11->s8+
         s11->s10+
         s12->s1+
         s12->s4+
         s12->s5+
         s12->s10+
         s13->s1+
         s13->s2+
         s13->s4+
         s13->s7+
         s13->s10+
         s13->s12+
         s14->s1+
         s14->s3+
         s14->s4+
         s14->s5+
         s14->s7+
         s14->s10+
         s14->s12+
         s14->s13+
         s15->s0+
         s15->s1+
         s15->s2+
         s15->s3+
         s15->s5+
         s15->s6+
         s15->s7+
         s15->s8+
         s15->s9+
         s15->s10+
         s16->s4+
         s16->s5+
         s16->s6+
         s16->s11+
         s17->s0+
         s17->s2+
         s17->s4+
         s17->s7+
         s17->s8+
         s17->s9+
         s17->s13+
         s17->s14+
         s17->s15+
         s18->s2+
         s18->s3+
         s18->s4+
         s18->s6+
         s18->s10+
         s18->s12+
         s18->s15+
         s19->s0+
         s19->s2+
         s19->s4+
         s19->s5+
         s19->s7+
         s19->s10+
         s19->s14+
         s19->s15+
         s19->s16+
         s20->s0+
         s20->s2+
         s20->s3+
         s20->s4+
         s20->s7+
         s20->s9+
         s20->s12+
         s20->s13+
         s20->s16+
         s20->s18+
         s21->s0+
         s21->s1+
         s21->s2+
         s21->s4+
         s21->s8+
         s21->s9+
         s21->s10+
         s21->s11+
         s22->s0+
         s22->s1+
         s22->s2+
         s22->s5+
         s22->s6+
         s22->s7+
         s22->s15+
         s22->s16+
         s22->s20+
         s22->s21+
         s23->s1+
         s23->s2+
         s23->s9+
         s23->s12+
         s23->s13+
         s23->s16+
         s23->s17+
         s23->s20+
         s23->s22+
         s24->s0+
         s24->s2+
         s24->s3+
         s24->s4+
         s24->s5+
         s24->s9+
         s24->s11+
         s24->s12+
         s24->s13+
         s24->s16+
         s24->s17+
         s24->s19+
         s24->s21+
         s24->s23+
         s25->s0+
         s25->s1+
         s25->s4+
         s25->s9+
         s25->s10+
         s25->s13+
         s25->s14+
         s25->s15+
         s25->s16+
         s25->s19+
         s25->s21+
         s25->s23+
         s25->s24+
         s26->s0+
         s26->s1+
         s26->s5+
         s26->s6+
         s26->s8+
         s26->s9+
         s26->s11+
         s26->s14+
         s26->s15+
         s26->s16+
         s26->s17+
         s26->s18+
         s26->s19+
         s26->s20+
         s26->s25+
         s27->s2+
         s27->s5+
         s27->s9+
         s27->s10+
         s27->s12+
         s27->s15+
         s27->s16+
         s27->s18+
         s27->s20+
         s27->s25+
         s27->s26+
         s28->s0+
         s28->s1+
         s28->s4+
         s28->s7+
         s28->s9+
         s28->s12+
         s28->s13+
         s28->s16+
         s28->s18+
         s28->s19+
         s28->s20+
         s28->s21+
         s28->s22+
         s28->s23+
         s28->s24+
         s28->s25+
         s28->s26+
         s29->s0+
         s29->s3+
         s29->s5+
         s29->s6+
         s29->s8+
         s29->s11+
         s29->s17+
         s29->s19+
         s29->s21+
         s29->s24+
         s29->s26}
one sig r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29 extends Resource{}{}
fact{
resSucc=r2->r0+
         r2->r1+
         r3->r1+
         r4->r0+
         r4->r3+
         r5->r0+
         r5->r2+
         r5->r3+
         r5->r4+
         r6->r2+
         r6->r5+
         r7->r0+
         r7->r2+
         r7->r4+
         r7->r5+
         r7->r6+
         r8->r1+
         r8->r2+
         r8->r6+
         r9->r1+
         r9->r2+
         r9->r4+
         r9->r8+
         r10->r1+
         r10->r4+
         r10->r5+
         r10->r6+
         r10->r8+
         r11->r2+
         r11->r7+
         r11->r9+
         r11->r10+
         r12->r2+
         r12->r4+
         r12->r5+
         r12->r6+
         r12->r7+
         r12->r8+
         r12->r11+
         r13->r2+
         r13->r4+
         r13->r6+
         r13->r7+
         r13->r8+
         r14->r0+
         r14->r1+
         r14->r2+
         r14->r8+
         r14->r9+
         r14->r12+
         r14->r13+
         r15->r0+
         r15->r2+
         r15->r3+
         r15->r5+
         r15->r6+
         r15->r8+
         r15->r11+
         r15->r13+
         r16->r1+
         r16->r2+
         r16->r6+
         r16->r7+
         r16->r8+
         r16->r9+
         r16->r11+
         r16->r12+
         r16->r14+
         r17->r0+
         r17->r3+
         r17->r4+
         r17->r8+
         r17->r9+
         r17->r11+
         r17->r12+
         r17->r14+
         r17->r15+
         r18->r0+
         r18->r3+
         r18->r4+
         r18->r9+
         r18->r10+
         r18->r11+
         r18->r16+
         r19->r0+
         r19->r2+
         r19->r3+
         r19->r4+
         r19->r5+
         r19->r7+
         r19->r8+
         r19->r10+
         r19->r11+
         r19->r12+
         r19->r13+
         r19->r15+
         r19->r17+
         r20->r2+
         r20->r10+
         r20->r11+
         r20->r13+
         r20->r16+
         r20->r17+
         r20->r19+
         r21->r1+
         r21->r3+
         r21->r4+
         r21->r5+
         r21->r7+
         r21->r8+
         r21->r9+
         r21->r13+
         r21->r20+
         r22->r1+
         r22->r2+
         r22->r5+
         r22->r6+
         r22->r7+
         r22->r12+
         r22->r14+
         r22->r16+
         r22->r17+
         r22->r19+
         r23->r0+
         r23->r2+
         r23->r3+
         r23->r6+
         r23->r8+
         r23->r10+
         r23->r17+
         r23->r18+
         r23->r19+
         r24->r0+
         r24->r1+
         r24->r2+
         r24->r4+
         r24->r7+
         r24->r9+
         r24->r10+
         r24->r13+
         r24->r15+
         r24->r16+
         r24->r17+
         r24->r18+
         r24->r20+
         r24->r21+
         r24->r23+
         r25->r0+
         r25->r1+
         r25->r2+
         r25->r13+
         r25->r14+
         r25->r16+
         r25->r17+
         r25->r20+
         r25->r21+
         r25->r22+
         r25->r23+
         r26->r0+
         r26->r1+
         r26->r3+
         r26->r4+
         r26->r5+
         r26->r6+
         r26->r10+
         r26->r12+
         r26->r13+
         r26->r17+
         r26->r18+
         r26->r19+
         r26->r20+
         r26->r21+
         r26->r22+
         r26->r23+
         r26->r25+
         r27->r0+
         r27->r1+
         r27->r2+
         r27->r3+
         r27->r6+
         r27->r9+
         r27->r13+
         r27->r14+
         r27->r15+
         r27->r17+
         r27->r18+
         r27->r19+
         r27->r22+
         r27->r26+
         r28->r1+
         r28->r3+
         r28->r7+
         r28->r8+
         r28->r11+
         r28->r13+
         r28->r15+
         r28->r16+
         r28->r18+
         r28->r19+
         r28->r20+
         r28->r21+
         r28->r22+
         r28->r23+
         r28->r24+
         r29->r0+
         r29->r1+
         r29->r3+
         r29->r5+
         r29->r11+
         r29->r15+
         r29->r17+
         r29->r18+
         r29->r19+
         r29->r21+
         r29->r22+
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
one sig req0 extends Request{}{
sub=s0
res=r0
}
//**********************
//***      Rules     ***
//**********************
one sig rule0 extends Rule{}{
    s =s27
    t =r19
    m = prohibition
    p = 1
    c = c9+c3+c6
}
one sig rule1 extends Rule{}{
    s =s0
    t =r17
    m = permission
    p = 1
    c = c2+c9
}
one sig rule2 extends Rule{}{
    s =s5
    t =r22
    m = permission
    p = 0
    c = c3+c9+c0+c1
}
one sig rule3 extends Rule{}{
    s =s1
    t =r3
    m = prohibition
    p = 1
    c = c6+c9+c3
}
one sig rule4 extends Rule{}{
    s =s21
    t =r17
    m = permission
    p = 2
    c = c5+c3+c8
}
one sig rule5 extends Rule{}{
    s =s15
    t =r21
    m = permission
    p = 1
    c = c7
}
one sig rule6 extends Rule{}{
    s =s13
    t =r20
    m = permission
    p = 1
    c = c0
}
one sig rule7 extends Rule{}{
    s =s15
    t =r6
    m = permission
    p = 1
    c = c2+c9+c8+c3+c6+c7+c0
}
one sig rule8 extends Rule{}{
    s =s12
    t =r11
    m = permission
    p = 0
    c = c1+c2+c7+c5+c6+c4
}
one sig rule9 extends Rule{}{
    s =s23
    t =r20
    m = prohibition
    p = 2
    c = c8+c5+c4+c6+c3
}
one sig rule10 extends Rule{}{
    s =s9
    t =r10
    m = permission
    p = 3
    c = c6+c5+c0+c9+c7
}
one sig rule11 extends Rule{}{
    s =s24
    t =r5
    m = permission
    p = 3
    c = c2
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
