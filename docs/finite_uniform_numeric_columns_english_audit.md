# Track A — all old and skipped-original numerical-H columns in one common finite Henson future

**14 November 2026. English proof and hostile audit before Lean.**
This is independent of the currently checking numerical top-profile PR #161:
it starts from verified Track A [PR #157](https://github.com/janhubicka/lean-kk/pull/157)
and the previously merged literal numerical-H finite binary L laws.
No new existence assumption is introduced.

## Complete old-to-marked-top columns at all numerical generations

Fix a symmetric actual Henson original graph E, height k, finite numerical-H carrier cutoff M,
and a **single** pinned finite target embedding f of a full finite graph A over [0,b).
Let W be a finite set of target future indices, all in [b,N). Let tau:Nat→Fin d type W and
c:Nat→Fin d→Bool prescribe its COMPLETE old-index columns. Suppose:

- f(i)=i for every old i<b;
- every w∈W is genuinely mapped to a later original f(w)≥b;
- for every distinct i,j<N, E(f(i),f(j))=A(i,j) in the **specified orientation**;
- for all i<b and w∈W, A(i,w)=c(i,tau(w)).

Then for EVERY old original i<b, EVERY marked future w∈W and EVERY real generation q≤k,

```
L^H_{k,M}(iota_k(i,q), iota_k(f(w),k))
 = L^H_{k,M}(iota_k(f(w),k), iota_k(i,q))
 = c(i,tau(w)).
```

**Proof.** Since i<b≤f(w), i<f(w). The pinned identity gives
E(i,f(w))=E(f(i),f(w))=A(i,w)=c(i,tau(w)) by exact off-diagonal inducedness.
The already verified `numericH_older_generation_to_top_exact`, with q≤k, copies that exact
Boolean atom to the finite numerical-H L bit. The finite-H symmetry theorem copies the same
bit in reverse. Thus both positive bits AND all prescribed old-to-future nonedges survive
at **every** old real generation, including q=k.

This is simultaneous across all w∈W; nothing singles out a designated target.

## Complete omitted-original zero columns

Suppose also the pinned embedding supplies its strong real chronological gap invariant:

```
for every new target m in [b,N),
 for z<f(m) outside f([0,m)),
    E(z,f(m))=E(f(m),z)=false.
```

For any w∈W and any actual skipped original z<f(w) outside f([0,w)),
all q≤k give

```
L^H_{k,M}(iota_k(z,q),iota_k(f(w),k)) =
L^H_{k,M}(iota_k(f(w),k),iota_k(z,q)) = false.
```

Indeed z<f(w) opens the older-to-top generation gate at every q, and the original gap
column is false. The other L direction follows from original symmetry. In addition,
for every odd dummy address 2a+1, both directed L atoms toward the selected top are false
by the verified finite numerical-H odd-left/odd-right laws.

This makes the real/dummy distinction explicit and does NOT mistakenly claim that the
auxiliary H+ E relation of odd parameters vanishes.

## Actual uniform finite Henson future

The verified theorem `henson_leftDense_realizes_all_finite_relative_age_profiles`
constructs, from any fixed normalized Henson E, b, ell≥2, d>0 and complete c,
one pinned original f and one target W containing **ALL feasible normalized clique vectors**.
The target is the concrete old-prefix-plus-tagged-future graph from the earlier verified
encoding and compatibility theorems; hence the required
`A(i,w)=c(i,tau(w))` is a literal theorem of its definition.

Specializing the two propositions above yields one single physical future which
simultaneously has:
- all old-to-marked L atoms c(i,tau(w)) for every generation q≤k in BOTH orientations,
- all unselected intermediate real-original-to-marked L atoms false in BOTH orientations,
- all odd dummy L atoms toward selected top copies false,
- and all original finite feasible clique-vector witnesses (already verified by PR #157).

The numerical top-profile equivalence and a finite carrier cutoff M are addressed by
the independent PR #161. After both branches pass, these statements compose without
rechoosing the physical original embedding f.

## Hostile audit

1. **Full old prefix:** i<b means every old original including skipped parameter/gap originals
   already in the committed past; omitting these would break the mixed-clique safety.
2. **Both directions:** original symmetry, or an independent reverse-L theorem, is needed.
   A positive forward edge alone is not enough.
3. **Top gate is essential:** q may be any earlier generation ≤k but the future copy is
   at the TOP generation k. Arbitrary lower future generations need separate gates.
4. **Distinct i and w:** i<b≤w ensures distinct abstract labels, so the original induced
   equivalence applies without requiring E's loops to agree with A.
5. **Actual order:** i<f(w) and z<f(w) are strict original-index inequalities in the unchanged
   enumeration; abstract sorting of vertices is not substituted for them.
6. **Complete negative columns:** all zeros in c are preserved, not just the supported ones.
7. **Skipped gap condition:** z outside f([0,w)) excludes previously committed image vertices,
   whose edges may legitimately be positive; asserting all z<w are nonadjacent would be false.
8. **M semantics:** Boolean L equations are total even when addresses exceed finite carrier M;
   a literal physical substructure statement additionally needs the carrier cutoff, as in PR #161.
9. **No cross-gap E assertion:** odd dummy binary L zeros do not imply auxiliary Kpt E is zero.
10. **No universal diagram:** a uniform *finite* original future does not establish the infinitely
    coherent reserved/selected schedule or its full old reference-age invariant.
11. **All sorts at once:** w ranges over the entire universal marked future W; the typed columns
    are checked for each w, including sorts absent from the designated cover support.
12. **No BRD claim:** this bridge still does not establish parameter-closed I1–I3/B3,
    labelled inverse-source orbit, occurrence factorization or upper/lower big Ramsey numbers.

## Lean deliverables

Create `Kk/FiniteUniformNumericColumns.lean` on a branch stacked over #157, independent of #161.
Prove `finiteNumericH_pinned_old_generation_column_both`,
`finiteNumericH_pinned_gap_generation_zero_both`, and a single uniform finite Henson corollary
with no unverified existence premise.
Require an explicit exact-head new-module build, strict named standard-only transitive axioms
and full `lake build`. Track G owns integration and validation marks.
