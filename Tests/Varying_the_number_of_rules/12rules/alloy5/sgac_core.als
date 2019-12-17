open util/relation
module sgac_core
////////////////////////////////////////////////////////
// 						SGAC 											 //
////////////////////////////////////////////////////////
sig Subject {
	subSucc : set Subject                  //  subject successors; covering pair (s1,s2) in subSucc <=> s1 son of s2, then, s1 plus specific than s2; s2 father of s1
}
fact { acyclic[subSucc,Subject] }

sig Resource {
	resSucc : set Resource                 // resource successors; covering pair
}
fact { acyclic[resSucc,Resource] }

abstract sig Modality {}
one sig prohibition, permission extends  Modality {}
sig Context {}
sig Rule {
	p : one Int,         	 // priority of the rule
	s : one Subject,
	t : one Resource,
	m : one Modality,
	c : set Context 			// truth table of the condition
}{
  p >= 0
}

sig Request{
sub: one Subject,
res: one Resource,
ruleSucc:  Rule -> set Rule
}{
no sub.subSucc
no res.resSucc
Rule.ruleSucc in applicableRules[this]
ruleSucc.Rule in applicableRules[this]
}

fact {
// definition of ruleSucc r1 -< r2
//    for Rule
	all req: Request |
		all r1,r2 : applicableRules[req] |
			r1 in req.ruleSucc.r2 // r1 -> r2 r2 plus prioritaire donc
			<=>
           isPrecededBy[r1,r2]
 //        and
 //          not (some r3 : applicableRules[req] | isPrecededBy[r1,r3] and isPrecededBy[r3,r2] )
}

////////////////////////////////////////////////////////
// 							FORMULAS									 //
////////////////////////////////////////////////////////


pred evalRuleCond[r:Rule,con:Context]{
con in r.c
}

////////////////////////////////////////////////////////
// 						AUXILIARY FUNCTIONS					 //
////////////////////////////////////////////////////////

pred lessSpecific[r1,r2: Rule]{ // lessSpecific[r1,r2]=TRUE => r2 has precedence over r1 (subject wise or priority)
	(r2.p < r1.p)
	or
	(
		r2.p = r1.p
			and
		r2.s in (r1.s).^subSucc
	)
}
/*
pred applicableRule[r:Rule]{
Request.sub in (r.s).*subSucc
and Request.res in (r.t).*resSucc
}
*/

fun applicableRules[req:Request]: set Rule{
{r: Rule | req.sub in (r.s).*subSucc and req.res in (r.t).*resSucc}
}


pred maximal[r:Rule]{
no r1 : Rule | lessSpecific[r,r1]
}

pred isPrecededBy[r1,r2:Rule]{
	(
 		lessSpecific[r1,r2]
		or
		(
			not lessSpecific[r2,r1]
			and
			maximal[r1]
			and
			maximal[r2]
			and
			r2.m = prohibition
			and
			r1.m != r2.m
		)
	)
}

pred sinkRule[r:Rule,req:Request]{
no r.(req.ruleSucc)
}


run{} for exactly 4 Rule, 4 Subject, 4 Resource, 4 Context, 2 Request

assert acyclicRule{ all r: Request | acyclic[r.ruleSucc,applicableRules[r]]}
check acyclicRule for  7 but exactly 5 Rule