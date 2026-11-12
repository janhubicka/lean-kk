# Universal finite future pool from all feasible normalized clique vectors

**12 November 2026. English proof and adversarial audit, committed before Lean.**

## Exact construction, no geometric hypotheses

Fix ell>0, a finite sort set Fin d, and **arbitrary** nonnegative raw integer support bounds B on the existing type IntegerGraphSupport d ell. The finite set of feasible normalized vectors is
\[
V_B=\{w:\operatorname{IntegerCliqueWeights}(d,\ell):
   \forall T,\operatorname{integerCliqueOnSupport}(w,T)\le B(T)\}.
\]
It contains the all-zero vector when ell>0 (theorem already checked in PR #85).

For each feasible w, let C_w be the **complete L-clique** on the genuine dependent type \(\operatorname{IntegerWitnessVertex}(w)=\sum_{j:\operatorname{Fin}d}\operatorname{Fin}(w_j)\), already kernel-verified in PR #82. We construct one common **finite** vertex type
\[
U=\sum_{w:\operatorname{IntegerCliqueWeights}(d,\ell)}
  \operatorname{IntegerWitnessVertex}(w).
\]
Define the component \(C_w\subseteq U\) as the image of \(v\mapsto(w,v)\), and the future pool \(W_B=\bigcup_{w\in V_B}C_w\). Its directed ordinary-L Boolean edge table is
\[
 E((w,v),(w',v'))=1
  \quad\Longleftrightarrow\quad w=w'\ \text{and }(w,v)\ne(w',v').
\]
This is symmetric and irreflexive. Components of different vector indices have no edges in either direction, while each C_w is complete. Components may be empty (when w=0), but the vertex pool remains finite.

**Target:** every directed clique s⊆W_B is contained in one feasible component C_w. Hence |s|<ell, and on every admissible support T the number of vertices whose sort lies in T is ≤B(T). Conversely for **every** feasible vector w the full component C_w is a directed clique whose labelled support counts on each T are **exactly** integerCliqueOnSupport(w,T).

It follows that the set of normalized labelled clique-count vectors **realized inside this one common finite future graph** is exactly V_B. This is a genuine strengthening of the earlier per-coordinate maximizers; it removes the finite *ordinary-L* “fixed future W may be too small” obstacle by choosing a universal W_B. It does not claim such W_B already exists as a prescribed relative extension inside the numerical-H scaffold.

## English proof

1. **Finite component and exact counts.** The fibre Sigma-type is finite. For a fixed w, the component injection \(\operatorname{IntegerWitnessVertex}(w)\hookrightarrow U\), \(v\mapsto(w,v)\), is injective. Thus \(|C_w|=\sum_jw_j<\ell\). The support-filtered cardinality equals \(\sum_{j\in T}w_j\) by the verified complete-component support theorem and preservation of cardinalities under this injective image.
2. **Clique classification.** Let s⊆W_B be a directed clique. If s=∅, choose w=0. Otherwise choose u∈s. Since u∈W_B, it belongs to some C_w. For any v∈s with v≠u, the directed clique condition E(u,v)=1 forces the same first coordinate w. Since v is itself in W_B, this means v∈C_w. Consequently s⊆C_w.
3. **No forbidden clique.** By classification, |s|≤|C_w|<ell. This holds at every ell>0, including the empty-clique case.
4. **No spurious support bounds.** For every T, the T-labelled vertices of s form a subset of those of C_w. Their cardinality is therefore at most \(\sum_{j\in T}w_j\le B(T)\).
5. **Every feasible vector is realized.** For each w∈V_B, its C_w is a full complete clique contained in W_B, with exactly w_j vertices of each sort and hence support sums equal to the exact normalized vector. The empty vector is represented by the empty clique.

## Adversarial audit

- **The finite graph is selected, not universal by default.** This construction deliberately creates W_B; an arbitrary previously fixed W may fail to realize even one allowed positive vector.
- **No symmetry assumption is hidden.** E is explicitly symmetric and loop-free. The directed clique predicate checks both orientations.
- **No cross-component clique.** The condition w=w' in E is essential. Allowing even one edge between distinct components can create forbidden mixed cliques.
- **Repeated sorts are genuine distinct vertices.** C_w is a Sigma of labelled slots, not a subset of the support T.
- **Empty vector/components.** For ell>0 the all-zero normalized vector is feasible for every B, but C_0 is empty. Every s=∅ is a clique, so its count vector is still realized.
- **ell=0 phantom.** At d=ell=0 the subtype of normalized weights may be inhabited through truncated subtraction while no graph is K_0-free. Restrict the no-K_ell theorem to ell>0.
- **ell=1.** No admissible nonempty support exists. Every vector has zero total weight, so W_B is empty and the empty clique has size <1.
- **Arbitrary B.** B need not itself be a graph age. The set V_B and canonical G_B are defined nonetheless.
- **All bounds jointly.** Each component index w must satisfy *every* support inequality, not merely one chosen maximizing coordinate.
- **Same-component membership must be proved, not assumed.** The proof needs the fact that every vertex of the chosen W_B belongs to at least one **actual** image C_w; equality of first indices then identifies that component.
- **No old graph P.** Attaching a fixed P with prescribed old-to-new bits may invalidate K_ell-freeness even though W_B alone is K_ell-free.
- **No reserved Q_T yet.** This stage does not attach the support-testing clique blocks Q_T; that is the next physical L-only construction.
- **Not full corrected B3.** The ordinary graph E is not the H+ auxiliary parameter-incidence E and does not determine the complete I1/I2/I3/B3 source or a labelled common inverse source.
- **No fake finiteness of full Henson graph.** The construction is a finite model; embedding it in the countable Henson graph over a particular old prefix is a separate relative age/extension theorem.

## Lean implementation

Use the already verified dependent type IntegerWitnessVertex w and feasible-vector Finset. Define \`UniversalWitnessVertex d ell := Σ w, IntegerWitnessVertex w\`, \`universalWitnessComponent w\` as the image of \`Sigma.mk w\`, \`universalWitnessFuture B\` as the Finset.biUnion over feasible weights, and \`universalWitnessEdge\` with the literal same-index/different-vertex Boolean rule.

Prove an injectivity and cardinal/support transfer for each component, exact clique isolation, the single-component classification for any nonempty clique, K_ell-freeness, no spurious B constraints, and realization of every feasible component. Run the complete pinned Lean build and strict named transitive-axiom audit. Do not mark the Henson relative-realization/parameter-closed assertions green on this basis.
