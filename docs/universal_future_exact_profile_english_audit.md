# Exact realised extension profile of the universal finite future (ordinary L only)

**12 November 2026 — English-first proof and adversarial audit.** This note is deliberately committed before the Lean code. It applies to the **actual** finite dependent-sum graph constructed in \`Kk/UniversalFutureDisjointCliques.lean\`, already merged in PR #86 and hosted-verified, and the actual canonical integer-age definitions.

## Main theorem

Fix a finite sort set \`Fin d\`, a threshold \`0<ell\`, and an arbitrary raw support-bound function \`B : IntegerGraphSupport d ell → Nat\`. Let \`W_B\` be the **single** common finite future of every B-feasible normalized clique vector, with actual ordinary-L edge \`universalWitnessEdge\`. For any normalized labelled vector \`w : IntegerCliqueWeights d ell\`:

\[
\boxed{\quad w\in V_B\quad\Longleftrightarrow\quad
   \exists s\subseteq W_B\;(\operatorname{Clique}_{L}(s)\ \land\
   \forall T\in\operatorname{IntegerGraphSupport}(d,\ell),\
   |\{v\in s:\operatorname{sort}(v)\in T\}| =
     \operatorname{integerCliqueOnSupport}(w,T)).\quad}
\]

The right side demands equality of **all admissible support counts at once**, not only one chosen T. The graph \`W_B\` is specific and constructed; this is not a claim about arbitrary fixed future pools or any fixed old Henson prefix.

### Proof, feasible ⇒ realised

For w∈V_B choose the literal component C_w from the verified theorem \`universalWitnessFuture_realizes_every_feasible\` (PR #86). It is a directed clique of the actual \`universalWitnessEdge\`, lies inside W_B, has total cardinality <ell and matches \`integerCliqueOnSupport(w,T)\` for every admissible T simultaneously. Use s=C_w.

### Proof, realised ⇒ feasible

Take s⊆W_B a directed clique matching w on every T. The checked theorem \`universalWitnessFuture_clique_respects_raw\` (PR #86) shows that the support count of s is ≤B(T) for each admissible T, with **no separate compatibility assumption**. Substitute the matching equalities. Thus \`WitnessRespects integerCliqueOnSupport B w\`, which is exactly \`w∈feasibleIntegerCliqueVectors d ell B\`.

**Important:** The proof never assumes that a clique cannot be empty, that w is a nonzero vector, that different supports require the same maximizing component, or that B is already canonical. The existence of the zero vector for ell>0 was verified in PR #85.

## Canonical maximum realised in the same finite future

For every admissible support T, the actual integer canonicalizer is
\(G_B(T)=\max_{w∈V_B}\operatorname{integerCliqueOnSupport}(w,T)\).
The previous result and the individually concrete maximizer (PR #85) therefore give

\[
G_B(T)=\max\Bigl\{
  |\{v\in s:\operatorname{sort}(v)\in T\}| :
  s\subseteq W_B,\ s\text{ a directed }L\text{-clique}
  \Bigr\}.
\]

To prove its **upper inequality**, use the verified single-component classification \`universalWitnessFuture_clique_in_feasible_component\`: s lies in some C_w with w feasible. Its support size is at most that of C_w, equal to w(T), and feasibility of w implies w(T)≤G_B(T) by the standard \`witnessValue_le_canonical\` theorem. To prove the **lower inequality**, take the canonical maximizer w_T supplied by PR #85; C_{w_T} is an actual clique in W_B with support size exactly G_B(T). This argument does **not** claim a single clique attains G_B at every T: w_T is permitted to depend on T.

For Lean engineering the elementary upper and lower inequalities can be separate named endpoints before taking the finite supremum of the powerset filter. All proof terms should use \`Finset\` powersets and the existing universal directed-clique predicate, not a replacement graph model.

## Adversarial audit

1. **Fixed W versus constructed W_B:** a previously arbitrary future W need not realise all vectors; the merged one-sort empty-future regression proves the failure. The right side is specific to W_B.
2. **Complete profile, not one coordinate:** matching only one support T does not make w feasible; a different support U may violate B(U). Quantify over ALL supports on both sides.
3. **Repeated sort labels:** the component has w_j distinct slots of label j; cardinalities count multiplicity, not occupied sorts.
4. **Zero vector:** the empty clique realises the zero vector even when C_0 is empty. If d=0 all supports are empty and the iff is still well-formed when ell>0.
5. **ell=1:** no nonempty admissible supports exist. The only normalized vector is zero; W_B has no vertices. The iff remains valid and must not invent singleton supports.
6. **ell=0:** the theorem's positivity premise is essential, because the normalized subtype can be degenerate at d=0 and a \`K_0\`-free graph cannot exist.
7. **Arbitrary raw B:** no assumption that B itself satisfies graph-age consistency; only its feasible-vector system and canonicalization are used.
8. **No spurious realization from a subclique:** a subclique of C_w yields a coordinatewise smaller vector which remains feasible because the B-support constraints are upper bounds. This is already the core of the merged \`universalWitnessFuture_clique_respects_raw\` proof.
9. **Directedness matters:** the actual graph \`universalWitnessEdge\` is symmetric and loop-free, and the clique predicate checks all ordered pairs.
10. **Distinct components have no cross L edges:** otherwise a clique could mix two different w-components and violate raw support constraints; this is checked in the merged \`universalWitnessClique_single_component\`.
11. **Canonicalizer vs raw equality:** equality of realised feasible profiles determines G_B, not B pointwise if B is noncanonical. This is why the canonical-maximizer statement targets G_B(T).
12. **No common maximizer across supports:** the existence of one C_w per w is essential; do not pick just one w_T and claim it works for all T.
13. **No relative Henson conclusion:** this is a stand-alone finite L graph, with no required past P, reserved blocks Q_T, gap G, auxiliary Kpt E, or parameter-closed upper L+ types. Attaching the support-testing reserved blocks and proving all relative old-to-future certificates remain separate.
14. **No misleading global progress marker:** completing this finite ordinary-L age representation does not establish the common labelled inverse-source orbit or the unconditional upper BRD bound.

## Formalisation and validation contract

Prove the exact iff in the existing \`Kk\` namespace using \`Kk.universalWitnessFuture_realizes_every_feasible\` and \`Kk.universalWitnessFuture_clique_respects_raw\`. Then prove an upper support-count bound by the **same-component feasible-index theorem** plus \`witnessValue_le_canonical\`; prove a lower bound using the already verified \`integerGraphAgeCanonical_has_feasible_maximizer\`, with s=C_w. Finally derive equality with the actual finite supremum over clique subsets if useful.

All new endpoints must pass a pinned complete Lean project build and exact standard-only transitive-axiom parser gate. Do not add a manuscript green mark for numerical-H/Kpt relative realization.
