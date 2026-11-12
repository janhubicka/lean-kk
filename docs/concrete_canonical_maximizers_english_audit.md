# Concrete clique maximizers of arbitrary raw integer-age bounds

**12 November 2026. English-first proof and hostile audit; Lean follows.**

## Mathematical problem

The manuscript's editable extension-profile lemma now correctly identifies an abstract graph age F from the full profile of permitted labelled finite cliques. The Lean canonicalizer \`integerGraphAgeCanonical d ell B\` is defined for *any* raw bound B, using the finite supremum of all normalized multiplicity vectors w respecting every B(U). The previously merged complete typed-component theorem \`integerWitnessVertex_support_eq_integerCliqueOnSupport\` realizes any particular w as a literal finite complete ordinary-L graph on the dependent finite vertex type \`Σ j:Fin d, Fin w_j\`.

What remains for this isolated step is to show **that for every coordinate T the canonical maximum is attained by a concrete complete labelled clique**. It must be done without assuming B is an age, and without claiming that the same component simultaneously maximizes every support T.

## Exact statement

Fix ell>0, d finite, and arbitrary \`B : IntegerGraphSupport d ell → Nat\`. Write
\[
\mathcal W_B=\{w\in \operatorname{IntegerCliqueWeights}(d,\ell):
  \forall U,\ \operatorname{integerCliqueOnSupport}(w,U)\le B(U)\}.
\]
Then:

1. The zero vector \`0∈W_B\` (all coordinates represented by \`0 : Fin ell\`) is normalized and feasible. This requires ell>0.
2. For every T in the exact \`IntegerGraphSupport d ell\`, there is \(w_T∈\mathcal W_B\) with
\[
\operatorname{integerCliqueOnSupport}(w_T,T)
  = G_B(T) = \max_{w∈\mathcal W_B}\operatorname{integerCliqueOnSupport}(w,T).
\]
3. The complete typed clique \`IntegerWitnessVertex w_T\` has strictly fewer than ell vertices, and its T-labelled vertices have exact cardinality \`G_B(T)\`.
4. In **every** complete typed component of any feasible w, not just w_T, every subclique s of its vertices obeys
\[
|\{v∈s:\operatorname{sort}(v)∈U\}|\le B(U)
\]
for every permitted U. In particular, taking an induced complete graph does not create spurious feasible support counts.

## English proof

For (1), ell>0 provides \`0 : Fin ell\`. Its coordinate sum is 0, and every support sum is 0, hence satisfies the normalized total-size bound and all nonnegative B(U) bounds.

For (2), \`W_B\` is a finite nonempty set because the normalized vector type is finite and (1) provides a member. Its supremum of T-counts is therefore **attained** by some w_T. The supremum agrees definitionally with the existing \`integerGraphAgeCanonical d ell B T\`.

For (3), \`IntegerWitnessVertex w_T = Σ j, Fin (w_T)_j\` carries exactly \(\sum_j (w_T)_j\le\ell-1\) vertices. It is a complete symmetric irreflexive ordinary-L graph by \`integerWitnessCompleteEdge\`. The verified support-cardinality theorem gives exactly its vector's T-count, which by (2) equals \`G_B(T)\`.

For (4), every subset s of that component has no more U-sorted vertices than the entire component. Its full component count equals the integer support sum of w, which is ≤B(U) by feasibility. Thus the inequality holds for every subclique, including the empty one. Completeness of the component makes every subset a clique, but the cardinality inequality itself does not need any edge assumptions.

## Adversarial checks

- **Distinct maximizers per support.** The construction chooses w_T *depending on T*. It does NOT assert one vector simultaneously attains G_B at all supports; that is usually false.
- **Raw B need not be an age.** The statement computes the canonicalizer G_B from feasible vectors. No inference that B=G_B or that raw individual bounds equal their canonical values.
- **All-support feasibility.** Membership in W_B checks *every* admissible support U, not just T, and therefore avoids the false single-support canonicalization step.
- **ell=0 failure.** The zero vector cannot be defined coordinatewise as \`Fin 0\` when d>0, and the empty-Sigma phantom vector when d=0 does not satisfy a strict \<ell size bound. Keep \`0<ell\` in theorems that claim a real empty or complete component of size \<ell.
- **ell=1 boundary.** No nonempty support has size≤0, so the coordinate-indexed theorem is vacuous. The zero vector remains valid; no fake singleton support is fabricated.
- **d=0 boundary.** Supports are empty; the maximum-for-every-T statement is vacuous, and the all-zero vector still exists when ell>0.
- **Repeated sorts.** \`IntegerWitnessVertex w\` contains exactly w_j *distinct* vertices of sort j, including repeated labels. Counting occupied sorts alone is wrong.
- **Graph semantics.** The constructed edge is ordinary binary L, NOT auxiliary Kpt E, and the component is a standalone finite graph, not automatically an extension over an old Henson prefix.
- **No common W yet.** Per-support maximizers are different components in general. Free amalgamating them into a single graph (and then adding all Q_U reserved blocks) is a later construction, not a consequence of the maximizer lemma alone.
- **Relative incompatibility remains.** Even a standalone K_ell-free complete clique of size \<ell can fail to be compatible with required old adjacency: for ell=3, two new vertices both adjacent to one fixed old vertex cannot be adjacent to one another.
- **Canonical profile still not B3.** Complete L-only clique patterns do not determine the auxiliary E/parameter-closed full AlgorithmRun, nor the labelled inverse-source orbit.

## Planned Lean endpoints and validation

1. \`zeroIntegerCliqueWeight\` plus proof of \`WitnessRespects\` and membership of the genuine \`feasibleIntegerCliqueVectors\` Finset.
2. \`integerGraphAgeCanonical_has_concrete_maximizer\`: for each T, a concrete complete component whose T support count is exactly the canonical value G_B(T), retaining the entire feasible-vector conjunction.
3. \`integerWitnessComponent_subclique_respects_B\`: all subsets of any B-feasible complete component satisfy all B(U) bounds.
4. Optional derived \`concrete_components_determine_genuine_age\`: for genuine F, the maximum over these concrete feasible components is F(T), using the already verified fixed-point theorem.

Verify exact pinned local Lean if available; regardless, require the full hosted build and named standard-only axiom audit. No new manuscript green marker about numerical-H relative realization or corrected (B3) until the physical extension construction is supplied.
