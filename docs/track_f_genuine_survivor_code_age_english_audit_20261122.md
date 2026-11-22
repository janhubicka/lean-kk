# Track F — actual zero-code age equality from genuine surviving fronts (no dummy branch)

22 November 2026, evening. English proof and adversarial audit written BEFORE Lean.

## Main improvement

Earlier Track F numerical pre-code age rigidity used three complete same-dimension fronts OLD ≤ PRE ≤ FAR and an artificial later continuation of the coded branch j. That bookkeeping is unnecessary and potentially misleading in a diary: j really terminates at the code. We derive the full pre-code profile equality directly using the TRUE surviving target front indexed by Fin(d), while OLD/PRE are indexed by Fin(d+1).

Take an actual ordinary target graph E and genuine Henson K4 type tuples

  old, pre : Fin(d+1) → HensonOneType(4,E),
  later : Fin(d) → HensonOneType(4,E),

with levels m,c,H respectively, m≤c≤H, old_i≤pre_i for every old sort, and pre_{f(i)}≤later_i for every survivor i, where f=Fin.succAboveEmb j deletes precisely the selected coding sort j.

Assume the COMPLETE canonical normalized integer graph ages of the **old surviving target subtuple** old∘f at m and the genuine later survivors at H are numerically EQUAL on all nonempty supports. This is the endpoint conclusion now available by combining the independent source–target numerical theorems of merged PR #482 with the checkpoint invariant and the exact same target-order f.

Assume also rank(old_j)=rank(pre_j)=0 (the manuscript's rank-one code), and the precise legal zero-code law on the old full canonical age: for every nonempty admissible mixed support T containing j, F(T)=F(T.erase j). The singleton T={j} is handled separately.

**Conclusion:** the COMPLETE true pre-code canonical integer age at level c is IDENTICAL, support-by-support, to the genuine old full age at level m. Includes every two/three-sort mixed support, not just selected or pair projections. No later "dummy" type at coded j appears in the statement or proof.

## Proof, English first

1. **Genuine survivor chronological sandwich.** Restrict actual OLD/PRE target families along f to Fin(d). We now have genuine actual chronological fronts old∘f ≤ pre∘f ≤ later at levels m≤c≤H, and equal endpoint canonical numeric ages by hypothesis. Apply the already checked complete chronological age sandwich theorem (merged #438) directly on Fin(d), obtaining

  Canonical(pre∘f,c) = Canonical(old∘f,m)

on **every** nonempty admissible survivor support.

2. **Pull back to the full labelled pre-code support domain.** The checked physical canonical survivor reindexing theorem (merged #475) gives, for each survivor support U,

  Canonical(pre,c)(f[U]) = Canonical(pre∘f,c)(U)
  Canonical(old,m)(f[U]) = Canonical(old∘f,m)(U).

To derive agreement on EVERY old full support S which does not contain j, use the genuine order-preserving finite injection f and the finite combinatorial lemma

  j ∉ S ↔ ∃ U : IntegerGraphSupport(d,4), f[U] = S.

The reverse implication follows from Fin.succAbove_ne. For the forward implication, set U to trackFSelectedPreimage(f,S), whose image is exactly S intersect image(f). The Mathlib Fin.exists_succAbove_eq theorem says every old label distinct from j belongs to image(f), so the intersection equals S; nonemptiness and size ≤3 pass by injectivity. This finite support lifting is the ONLY extra finite-index lemma.

Thus the true P and F profiles on the full Fin(d+1) support domain agree whenever j∉S. No equality of mixed old/j supports is assumed.

3. **Actual pre-code graph-age consistency and antitonicity.** Genuine one-types at common level c yield IsIntegerGraphAge(d+1,4,P) by the checked actual-front canonical-age theorem (#436). The full old≤pre chronological extension implies P≤F by the checked full actual raw/canonical age antitonicity theorem (#438). This includes the coded coordinate and every mixed support, not only survivors.

4. **Coded singleton rank normalization.** For a genuine K4 Henson old/pre type of zero-based rank 0, the exact normalized canonical singleton is 1 by the checked physical singleton theorem (#472). Hence P({j})=F({j})=1. Do not confuse Lean rank zero with manuscript age one.

5. **Legal zero-code rigidity on all mixed supports.** Apply the checked domain-correct integer-age zero-code rigidity theorem (#430) to P,F. Its hypotheses have just been derived: P genuine, P≤F, complete survivor equality, correct singleton ones, and the old legal erasure law. Conclude P=F on ALL nonempty admissible supports, including j-containing triples. Empty erasure is never called.

## Additional source-to-target endpoint specialization

An optional short corollary may take a genuine SOURCE survivor age A_s and equalities

  A_s = Canonical(old∘f,m),
  A_s = Canonical(later,H).

Their transitive equality provides the endpoint hypothesis above. This is exactly the interface of the merged true source–target numeric K4 synchronization theorems (#482). The old source front/target sort map must refer to the SAME survivor labels; no hidden lexicographic reordering is allowed.

## Adversarial audit

1. Do not invent a dummy later type for the coded branch; the theorem only uses real later survivors.
2. The old and pre target fronts have d+1 entries; the later front has d. The injection f is exact Fin.succAboveEmb j, preserving TRUE target survivor order.
3. Fin.succAboveEmb must be INJECTIVE. Merging labels changes multiplicities and invalidates the canonical survivor reindexing theorem.
4. Every support avoiding j is the image of a support U, including triple supports. The forward proof uses Fin.exists_succAbove_eq; nonempty support and size≤3 are preserved.
5. Supports containing j are NOT images of f, and their equality is deduced by the legal zero-code and genuine age monotonicity, not by pretending deletion preserves them directly.
6. The coded singleton {j} is handled separately from its empty erasure; no value F(∅) is introduced.
7. Actual Henson target fronts must have genuine safe K3-free old-neighbour sets, not mere hypothetical colours; otherwise the age consistency lemma would fail.
8. Each old_i≤pre_i is full chronological bit extension (positive AND negative), not merely N(old_i)⊆N(pre_i).
9. Each surviving pre_{f(i)}≤later_i is also a genuine chronological extension, so the three-front sandwich is legitimate on the *target graph E itself*.
10. Numeric old/later endpoint equality is required for EVERY complete canonical survivor support, not just selected singleton or edge nonedge. The verified #482 can supply it after exact source/target checkpoint matching.
11. Numeric endpoint equality is not inferred from arbitrary raw equalities: #478/#482 recover canonical values from the complete finite sorted K4 class with actual Nat-labelled witnesses.
12. The old rank-zero and pre rank-zero are two separate premises, each tied to a genuine type. Source rank alone cannot set the target singleton without a compatibility argument.
13. The old legal zero-code F(T)=F(T.erase j) is a genuine requirement on each mixed admissible support, not an automatic consequence of rank zero.
14. d=0 is allowed. The surviving canonical graph-age domain is empty. The full old domain consists of one sort j; the singleton argument suffices. No Fin(0) selected survivor.
15. The final theorem is purely ordinary-L numeric age/chronology, not the full dependent Kpt E/parameter or B3 history. It does not rule out unintended meets/splits.
16. Global all-diary realization, 24-case interpretation, and BRD lower bound remain OPEN. The manuscript black proof and global pending marks must remain unchanged.
17. There is no need for chronological ordering of the induced source→target embedding e inside this local target proof. Application uses c=e(r) and separately verified actual target fibres.
18. The old/target lex-order matching must be carried explicitly when applying the result to a real diary, rather than identifying source and target coordinate enumeration by fiat.

## Acceptance gate

Prove two named Lean endpoints with no sorry, no new axiom:
(A) exact surjectivity of trackFMapSupport(Fin.succAboveEmb j) onto the nonempty bounded supports avoiding j;
(B) complete physical pre-code canonical age equality from true old≤pre≤later-survivor fronts, numeric survivor ENDPOINT equality, genuine zero ranks and legal code law. Add (C) optional source-mediated endpoint corollary.
Use existing strict named standard-only transitive-axiom report and full exact-head Lake build. Keep manuscript black proof frozen until the complete code-event geometry and target order are also assembled.
