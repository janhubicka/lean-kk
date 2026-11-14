# Track A — exact physical whole-prefix age, including canonical cover step

**14 November 2026. English proof and adversarial audit BEFORE Lean.**
Based on integrated `lean-kk/main` at commit
`498b83ec77871b5efd9c38c7a75491cbc261f6c9`.
All assertions here concern **ordinary graph L**, not the auxiliary
H+ Kpt E/source/parameter closure or a common inverse-source orbit.

## Setting: actual numbered numerical H, not a model reindexing

Let `E` be a symmetric Boolean original graph table, `k,M`
the numerical-H height and finite table size, and
`q(0)<...<q(r-1)` the actual nonconsecutive reserved original
labels forming a clique. Fix pivot `a<r` at generation `g≤k`,
with `r≤k+1`, and set

```text
m := iota_k(q(a),g)+1
W := {iota_k(j,k): j∈S}
Q := orderedReservedNumericPrefix k q a g
G := [0,m) \ (P∪Q).
cap := if g<a then a else a+1.
```

Here `S` is a finite set of later selected original labels and
`tau:Nat→Fin d` assigns sorts to their actual numerical top copies.
`T` is an admissible *nonempty* support `IntegerGraphSupport d ell`.
The physical numerical-H finite binary table is `L`.

Assume the actual **entire-front** conditions, as in the checked
`finiteNumericH_ordered_whole_prefix_marked_age_iff`:

* every selected original lies after every q(b); all q(b) form a
  clique, and the original uniform columns q(b)→every selected j
  equal the support bit `decide(tau(iota(j,k))∈T)`;
* P lies in [0,m); P→Q L atoms are zero; every *real* gap
  iota(i,t)∈G (t≤k) has E(i,j)=0 for every j∈S
  (odd dummy L bits vanish automatically);
* the entire actual L prefix [0,m) is K_ell-free;
* a separate Boolean reference table A agrees with literal L
  on all off-diagonal P×P and W×W pairs and has complete
  two-direction typed P×W columns `c(p,tau(w))`, identical to L.

No claim that a *fixed* W exhausts all abstract permitted labelled
clique configurations is made.

## Theorem I: exact raw canonical age at the physical cut

Let
`B_P(U):=ell−1−cap_A({p∈P:∀t∈U,c(p,t)=1})`,
the *actual old reference* raw bound calculated in PR #113.
For an arbitrary finite W with the above physical hypotheses,

```text
K_ell-free_L([0,m) ∪ W)
 iff
K_ell-free_A(W) and, for EVERY A-clique s⊆W and
EVERY nonempty support U,
  |s_U| ≤ G_(rawCliqueBlockBound ell cap B_P T)(U).
```

This is a **full jointly normalized clique-profile** statement,
not a single distinguished-capacity inequality.

### English proof

1. The verified `NumericPrefixWholeAge` theorem reduces the
   left-hand side exactly to
   `K_ell-free_A(P∪W) ∧ cap+cap_L(W_T)<ell`.
   Its proof already covers **every** odd dummy and real skipped
   numerical prefix coordinate via the exact complement G.
2. P and W are disjoint. Each p∈P is numerically at most
   the pivot iota(q(a),g); each w=iota(j,k) has j>q(a)
   and lies strictly after the pivot by the verified
   `hPosition_lt_of_block_lt`.
3. P is K_ell-free in A: it is a subset of [0,m) in L,
   which is K_ell-free by assumption; the exact old-old
   off-diagonal L=A table transfers the finite-clique test
   from L|P to A|P. Do not silently assume old A is safe.
4. Apply `finiteOldFuture_free_iff_canonical_support`
   to the actual disjoint P,W and complete two-direction typed
   columns. It gives
   `K_ell-free_A(P∪W) ↔ K_ell-free_A(W) ∧ C_(G_B_P)(W)`,
   where C_F(W) means all A-cliques in W respect ALL support
   bounds of F.
5. For K_ell-free W, the verified
   `finiteClique_all_constraints_integerCanonical_iff`
   identifies C_(G_B_P)(W) with C_(B_P)(W). This is a
   **whole-profile** equivalence, not a pointwise B_P=G_B_P claim.
6. The W_T clique capacity is the same for L and A: W_T is
   a subset of W and all off-diagonal W×W L atoms equal A,
   so exact induced-image capacity transport applies to the
   identity map on W_T.
7. The verified `finiteClique_full_constraints_canonical_block_iff`
   converts C_(B_P)(W) together with
   `cap+cap_A(W_T)<ell` into
   `C_(G_(rawCliqueBlockBound ell cap B_P T))(W)`.
   Its necessary guard cap<ell follows from cap≤r≤k+1
   only if r<ell; for Theorem I explicitly assume r<ell.
   This is not an implicit assumption about an arbitrary height k.
All equivalences are reversible, proving both directions.

Theorem I does **not** require B_P to be a genuine positive
graph age. If a raw singleton bound is zero, it is still an
exact combinatorial criterion, and its canonicalizer still
preserves the joint normalized feasible vectors.

## Theorem II: actual canonical cover effect (conditional)

Add genuine ages `lower ⋖ upper`, a designated support T, and
the original cover-block arithmetic hypotheses

```text
ell=lower(T)+r+1,
upper(T)=lower(T)+1,
r≥1.
```

Crucially add the **separate pointwise reference-age invariant**

```text
integerGraphAgeCanonical d ell B_P = upper.
```

This is a concrete, testable *entire-old-prefix* statement about
common old-neighbour capacities and all supports, not an
assertion that one selected sort's maximum matches.

Then the exact physical labelled continuation test is

```text
K_ell-free_L([0,m)∪W)
 iff
K_ell-free_A(W) and every A-clique s⊆W satisfies
  |s_U| ≤ (if cap<r then upper else lower)(U)
for EVERY admissible nonempty support U.
```

**Proof:** from Steps 1–4 above, the reference old/future age
is the complete upper profile because `G_B_P=upper`.
Transport the W_T capacity L→A as in Step 6. Apply the
already verified
`finiteClique_full_constraints_cover_step_iff`.
The required `cap≤r` follows from a<r:
if g<a, cap=a<r; otherwise cap=a+1≤r.
The cover arithmetic gives cap<ell. No claim of a false
pointwise equality of the physical enlarged raw bound
with the ideal single-support bound is used.

Only at the last reserved original (a=r−1), at generation
g≥r−1, can cap=r. All earlier coordinates have cap<r;
therefore the finite continuation profile changes from upper
to lower exactly at the prescribed pivot.

## Physical carrier qualification

The finite numerical-H Boolean L table is *total on Nat*,
including coordinates outside the carrier [0,M). To interpret
Theorems I/II as an actual finite H **substructure**, separately
require `iota_k(q(a),g)<M` and every selected
`iota_k(j,k)<M`; then the checked
`finiteNumericH_whole_prefix_and_top_in_carrier`
covers all tested coordinates. Neither condition should be
silently inferred from an abstract graph-age theorem.

## Adversarial audit / nonclaims

1. **Future W not universal by itself.** The theorem compares the
   actual L bits of one finite selected W to the reference A bits;
   it does NOT show a single physical W realizes all possible
   abstract sorted future graphs. The separate pinned-prefix
   theorem provides finite compatible realization *one pattern
   at a time*.
2. **P∩W disjointness must be derived** from the numerical cut and
   ordered selected originals; ignoring it invalidates
   old-plus-future clique-capacity arithmetic.
3. **Old A K-free is a derived premise**, not an assumption.
   It follows via old-P subset of safe full L prefix and
   complete off-diagonal old-old agreement. This explicitly
   protects against accidental use of the conditional
   finite reference-age theorem with an unsafe old graph.
4. **The capacity transport requires both directed future atoms.**
   Positivity preservation alone does not prove reverse
   transport of maximal directed clique capacity.
5. **r<ell matters for Theorem I.** The numerical-H height guard
   r≤k+1 does NOT imply r<ell unless ell,k are related.
   In Theorem II it follows from the cover equation.
6. **No raw-bound equality.** Inserting a support-T reserved
   block may lower raw capacities on proper sub-supports
   U⊊T. Only the feasible full system and its canonicalizer
   are equal to the ideal single-support cover step.
7. **Complete marked columns, including zeros.** The
   physical theorem assumes every future selected j has the
   prescribed q(b)-to-j bit, not just one target.
   The K3 P4 obstruction from PR #97 is still relevant.
8. **Past and gaps complete.** The entire numerical prefix
   includes odd dummies and every generation of every
   omitted original. The original real gap E-zero
   certificates remain explicit Track B obligations.
9. **Reference invariant is substantive.** Nothing in the
   finite gluing or pinned-prefix embedding theorem
   *automatically* proves G_B_P=upper for the actual
   recursively built old past. That is the remaining
   Track B induction invariant.
10. **No stronger H+ assertion.** E-incidence, parameter-closed
    corrected B3 microlevels and inverse-labelled source
    identification belong to other tracks.
11. **No BRD conclusion.** This finite local cover step is not
    the bounded resolved copy or occurrence-factorisation
    theorem of the circulation text.
12. **Zero-support boundary.** T is a genuine admissible
    nonempty `IntegerGraphSupport`, so d>0 and ell≥2
    follow from its existence. If the ambient support family
    is empty, there is no such cover step to instantiate.
13. **No superfluous symmetry of reference A.** The old/future
    calculation only uses complete *bidirectional crossing
    columns* and directed clique tests. The original E
    is symmetric because numerical-H L arcs must be symmetric.

## Lean validation plan

Create `Kk/NumericPrefixCanonicalCover.lean`, import
`Kk.NumericPrefixWholeAge`,
`Kk.FiniteOldColumnAge`,
`Kk.FiniteSupportCoverProfile`,
and `Kk.FiniteCliqueEmbeddingTransport`.
Prove an identity-map finite capacity transport lemma, then
Theorem I (raw canonical physical continuation) and Theorem II
(conditional genuine age-cover step).
Keep the user-visible assumptions explicit, with fully qualified
named `#print axioms` reports; demand an explicit new-module
build, the strict transitive-axiom parser and full lake build
at the exact feature-head. Do not touch `Kk.lean`,
`scripts/check_axioms.lean`, `kk.tex`,
`validation.tex`, or protected black manuscript text;
Track G owns integration and mark promotion.

## Exact unique cover-pivot normal form (separate arithmetic endpoint)

Let `a<r`. The sharp reserved prefix capacity is
`c(a,g)=a` for `g<a`, and `a+1` otherwise. Then

```text
c(a,g)=r  iff  a+1=r and a<=g.
c(a,g)<r  iff  a+1<r or g<a.
```

For the first equivalence, a strict lower generation gives capacity
a<r, hence cannot reach r. At a nonlower generation the capacity is
a+1, which reaches r precisely for the final original a=r−1.
The second equivalence is the corresponding strict inequality;
there is no other case because c(a,g)≤r. Both statements include
generation g=0 and height-irrelevant arithmetic, and need no
assumption about the original Henson graph.

Consequently the profile-valued function
`if c(a,g)<r then upper else lower` is *identically equal* to
`if a+1=r and a<=g then lower else upper`.
This is an exact order-theoretic normal form for the **conditional**
age-cover conclusion. It does NOT turn the hypotheses of the physical
composition theorem into unconditional schedule existence.
