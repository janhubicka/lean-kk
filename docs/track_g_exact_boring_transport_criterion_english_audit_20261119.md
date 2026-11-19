# Track G — exact old-boring criterion for preserving an entire chosen AlgorithmRun

19 November 2026. English proof and adversarial audit BEFORE Lean.

## Why a new criterion is needed

G365's physical no-novelty at old boring cuts, and G371's empty canonical Bad finite set, are sufficient conditions for transferring the SAME actual selected I and TOTAL monoid F to a larger source. They are not necessary: extra new crossing nodes might obey the SAME skip map. The exact condition should separate source interestingness from compatibility of the prescribed old total map.

## Theorem A (generic successor-tree, not Kpt-specific)

Fix one genuine successor-tree SMTree H, actual nested seeds X⊆Y, finite top t, and ONE genuine AlgorithmRun RX on X. Then the following are EQUIVALENT:

(1) There EXISTS an actual target AlgorithmRun RY on Y with RY.I=RX.I and RY.F=RX.F as TOTAL functions.

(2) At every cut i<t BORING for RX on the complete old pre-cut closure C_i=closure(S,RX.I(i+1),X), the complete target candidate closure D_i=closure(S,RX.I(i+1),Y) is also BORING, and there exists a genuine MMap Q_i satisfying all three conditions:
    - Q_i.map.SkipsOnly i;
    - for ALL z∈D_i with lev(z)>i, Q_i(ancestor(z,i))=ancestor(z,i+1);
    - RX.F(i) = MMap.comp H (RX.F(i+1)) Q_i.

**Strengthening after hostile audit:** the old actual skip factor at a boring cut is UNIQUE. If two total maps D,E both satisfy RX.F(i)=RX.F(i+1)∘D=RX.F(i+1)∘E, the verified `kpt_MMap_comp_left_cancel` proves D=E because RX.F(i+1) is injective. Thus Q_i is necessarily the old run's skip factor, not an independent choice. The exact transfer condition can be reduced to checking that very factor on the enlarged source. This is potentially weaker than physical no-novelty, and it is an equivalence.

## Proof of (1)→(2)

Let RY be the synchronized actual run. Fix an old-boring cut i. The old noninteresting-step law gives RX.I(i)=RX.I(i+1). If Y were interesting at i, the target actual interesting-step law would put i∈RY.I(i), and since RY.I=RX.I this yields i∈RX.I(i+1). But true selected-level bounds for RX.I(i+1) force i+1≤i, contradiction. Hence Y is boring. Apply RY.noninteresting_step to get the genuine Q_i and all three required skip, full target crossing and F equations, converting RY.I and RY.F to RX.I,RX.F by their literal equality. No source-profile equality is inferred.

## Proof of (2)→(1)

Define RY with I=RX.I, F=RX.F, topI=RX.topI and topF=RX.topF. At every target-interesting cut i, old X must also be interesting: otherwise (2) says target is boring. Reuse RX.interesting_step. At a target-boring cut, old X is also boring by verified monotonicity of the TRUE I1/I2/I3 test under source inclusion X⊆Y (proved in G365). Reuse RX's I(i)=I(i+1) equation, and use the Q_i supplied by (2) for the target full crossing and precise old F(i)=F(i+1)∘Q_i. These are exactly the target AlgorithmRun fields. Thus the SAME I,F define a genuine target run.

## Theorem B (explicit physical version)

For each old-boring i, instead of separately assuming the target is boring, assume:
(T) no target full Kpt terminal node at level i;
(M) no two target full-source nodes have an actual same-component meet of level i;
(Q) a genuine skip-only Q_i obeys every target full crossing ancestor equation AND the exact old F factor equation.
Then the full target I1 and I2 disjuncts are false and (Q) defeats I3's no-skip disjunct, so target is boring; apply theorem A. This is an explicit certificate in terms of true geometry and monoid compatibility, without assuming the stronger full physical no-novelty relation equality.

## Adversarial checks

1. The SAME actual top and SAME normalized successor tree H are essential; different cut-coordinate enumerations need another theorem.
2. X⊆Y gives TRUE old→new closure inclusion with identical I tails; interestingness is then monotone. Do not infer reverse monotonicity.
3. The target closure at i uses RX.I(i+1), not selected levels from an assumed arbitrary Y-run.
4. Existence of one synchronized Y-run is a choice of run, not uniqueness of arbitrary target F functions.
5. An old-boring step can change total F; preserving I alone does NOT make the old F equation automatically valid.
6. The compatible Q_i CANNOT differ from RX's original skip factor: left cancellation by injective RX.F(i+1) proves uniqueness. Requiring the original factor's action on new crossings is therefore exact.
7. Complete same-node crossing equations must include all dependent L+/E auxiliary records, no selected-front ordinary graph-age proxy.
8. At an old interesting cut no Q_i certificate is needed; monotonicity ensures it remains interesting.
9. The old-selected bound rules out an actual interesting Y-step that leaves the same selected I; it is crucial for necessity.
10. In the explicit physical variant, I2 is true competing same-component MEET at level i, not mere nonfunctionality of a selected old/upper map.
11. A target I1 terminal condition must be checked separately from crossing pairs.
12. Physical G365 no-novelty and empty E54 canonical Bad remain sufficient ways to prove the new exact criterion, but this equivalence does not imply they are necessary.
13. The K4 real auxiliary cuts 10 and 22 cannot be erased: if newly interesting, they violate the exact old-boring target criterion.
14. The theorem is finite-run and allows arbitrarily large source sets; it does not provide an effective uniform diary-level parameter bound.
15. It does not identify inverse images of different seeds under a common F nor an occurrence-independent labelled orbit.
16. Chronological cut reindexing, corrected B3 versus relative continuation, resolved infinite copy and sharp Kk-free big Ramsey bounds remain open.

## Lean plan

Formalize theorem A with exact iff, and theorem B with explicit terminal/meet/compatible-skip premises, both as standalone generic successor-tree statements importing verified G365. Direct exact-head Lake build, standard-only two-name qualified #print axioms gate and full Lean CI. Do not promote black manuscript.

## Theorem C — sharp old-factor physical criterion (after adversarial simplification)

In the setting of Theorem A, whole-run I/F transport exists **if and only if** at each old-boring cut (i) the enlarged source has no terminal node at the cut, (ii) it has no competing same-component meet at the cut, and (iii) **every** skip-only old factor D satisfying the actual old crossing law and old F-step factorization also satisfies the complete enlarged-source crossing law. Since the old factor exists by RX.noninteresting_step and is unique by G309, the universal quantifier is exactly a test of the *one* old factor, not an extra choice principle.

Forward: a synchronized target run must be boring and provides a target factor Q. Left cancellation identifies Q with any actual old factor D, so D also satisfies all target equations. Backward: take the actual old factor D; the stated extension certifies its Y-crossing equations. Absence of I1/I2 plus D's skip law defeats I3. The exact criterion from Theorem A builds a synchronized run.

This is a genuine tightening of the geometric critical path: **the corrected target condition is absence of new I1/I2 plus preservation of the unique old skip map's actual full Kpt crossing equations, not equality of entire physical crossing relations**. It allows new crossing pairs with the same specified continuation. Whether the resolved diary provides those equations remains open.
