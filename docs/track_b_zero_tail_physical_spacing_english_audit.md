# Track B — zero-tail physical spacing of finite canonical cover stages
**17 November 2026. English-first proof and adversarial audit.**

## Motivation

The successfully Lean-verified two-stage physical canonical-cover theorem builds two reserved original cliques Q0,Q1 in the same fixed Henson original graph. It carries the actual full old-to-future column c1 produced by Q0 into the second stage at the genuine cut F0. But top witnesses produced by the first stage may lie beyond F0, and its second reserved block is not guaranteed to follow all such witnesses. Merely postponing the second stage to a later cut N is INVALID without re-establishing the full pointwise old-prefix canonical age at N. The exact critical-original-count theorem identifies the obstruction.

Here is a useful conditional simplification **only at the ordinary-L old-age level**: artificially zero every new original's full typed future column after a chosen cut, while keeping the real Henson original graph E unchanged. This freezes the old support neighbourhood at that cut, so the exact old age stays constant through any later finite cut. One physical canonical-cover stage can then be placed arbitrarily far later. A second stage can be placed after an arbitrary number of intervening *original* indices while retaining both ordinary-L canonical age identities. The proof does NOT preserve previously selected positive witness columns beyond the cutoff.

## Statement 1 — zero-tail column and exact common-neighbour pool

Fix a positive future-sort dimension d, a cut b, and a *full* typed column c : Nat → Fin d → Bool. Set
\[
z_b(c)(p,t)=
 \begin{cases}
 c(p,t),&p<b,\\
 0,&p\ge b.
 \end{cases}
\]
For any actual later original cut N≥b and any admissible **nonempty** support U,
\[
 X_{[0,N),z_b(c)}(U) = X_{[0,b),c}(U)
\]
as literal **sets of original vertices**. Proof: every p<b sees exactly its previous full column and has unchanged membership; every b≤p<N has a zero column and therefore fails the requirement “positive to every sort in U” because U is nonempty. No hypothesis about the old original edge table E or forbidden cliques is used. The raw bound and its integer-witness canonicalization are consequently identical:
\[
 B_{[0,N),z_b(c)}(U)=B_{[0,b),c}(U),\qquad
 G_{B_{[0,N),z_b(c)}}=G_{B_{[0,b),c}}.
\]
Equivalently the full *actual* critical-original count of this column on the interval [b,N) is zero for every nonempty support.

**Sharpness:** the nonempty support assumption is essential. For the *empty* support, the “for every t∈U” predicate is vacuous and every new zero-column original joins the common-neighbour pool. The integer graph-age normalization correctly excludes empty supports. The whole old column c must stay fixed on p<b; changing old bits invalidates the equality.

## Statement 2 — a real physical cover at any prescribed later original cut

Assume the usual fixed-Henson/left-density hypotheses for the kernel-verified physical finite cover-stage theorem, a genuine integer graph-age cover lower ⋖ upper at supported T with the numerical r side equations, and an **actual pointwise full-prefix** age invariant \(G_{B_{[0,b),c}}=\mathrm{upper}\). For any N≥b, apply Statement 1 to obtain \(G_{B_{[0,N),z_b(c)}}=\mathrm{upper}\). Now invoke the actual finite physical cover theorem at N and with the whole zero-tail column z_b(c). It produces a genuine reserved original clique Q of size r, all its vertices q≥N and q<F, both-directed old-to-Q nonedges against *every* p<N, a complete gap-inclusive updated column, pointwise final canonical age lower, feasible integer clique vectors and a real uniform numerical-H positive-support top-stage witness. This places Q beyond any preselected finite set W of old originals with W⊆[0,N), while keeping E fixed and never assuming fake adjacency edits.

## Statement 3 — two finite covers with an arbitrarily long original-index gap

Take a real first physical cover step at cut b using original full column c. It yields Q0,F0, the genuine updated column
\[
c_1=\mathrm{supportBlockGappedColumn}(b,Q_0,T_0,c)
\]
and \(G_{B_{[0,F_0),c_1}}=\mathrm{middle}\). Fix any m≥0 and define
\[
N=F_0+m,\qquad
\widetilde c_1=z_{F_0}(c_1).
\]
Statement 1 gives the **derived** full old-prefix age at N: middle. Apply the second genuine physical cover theorem at N with the *entire modified* column \(\widetilde c_1\), rather than incorrectly applying it with c1. This gives Q1,F1 with Q1⊆[N,F1), complete old-to-Q1 nonedges (including all of Q0 and all m intervening original indices), and final canonical age lower. The two reserved blocks are nonadjacent in BOTH directed orientations. The first age equality at F0 and first positive-support top-stage witness still follow from the first theorem. The second age and uniform stage are actual finite statements in the unchanged original E.

## Adversarial scope audit

1. Zero-tail modifies **future typed passing columns**, not Henson original edges. It is legal for a new *abstract choice* of future-sort recipe, but may be incompatible with previously selected future witnesses that lie after F0.
2. If an earlier chosen finite witness w≥F0 is required to have positive passing bits to some active future sort, zeroing at F0 falsifies that requirement. Hence these spacing results **do not solve diary-selected witness coherence**. The stronger statement “Q1 comes after every first-stage positive witness while retaining all witness columns” requires separate certified zero-critical gaps under the ORIGINAL column c1, not the artificial z(c1).
3. Both finite canonical ages are evaluated at **fixed d** and exact full old typed columns. Splitting and coding can change the active sort domain; arbitrary across-dimension canonicalizer transport is unproved.
4. The first stage's witness may occur after F0 and before Q1; although it is a real vertex in E, its typed future-sort data in the second stage has changed. Do not claim one coherent selected embedding.
5. The first physical reserved block Q0 is below F0. The second block Q1 is above F0+m; complete old-to-Q1 isolation therefore implies genuine both-directed nonedges Q0×Q1 and against each of the m intervening original vertices.
6. An empty support would defeat the zero-tail pool identity; use genuine IntegerGraphSupport's nonempty witness.
7. No uniform bound on the physical original index F0/F1 is asserted, even with fixed m.
8. The theorem does not generate unbounded neutral intervals with the original columns unchanged. It only constructs an intentionally modified tail column.
9. There is no inference about dependent Kpt E, complete old/upper L+ I1/I2/I3/B3, auxiliary q2 cuts 10/22, and source-cut/labelled-orbit coherence.
10. All global BRD and resolved-copy claims remain pending.

## Verification policy

English proof committed first. The Lean endpoints should be independently exact-head compiled and have all transitive axioms registered, with only propext/Classical.choice/Quot.sound allowed. Mark manuscript only after verified, and place any additional preparatory result in olive text or appendix, leaving frozen black prose untouched.
