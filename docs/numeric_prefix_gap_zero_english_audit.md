# Track A — complete numerical-H prefix, real-or-dummy classification, and original gap-column transfer

**13 November 2026, English proof and adversarial review before Lean.**
This is a *new* independent Track A branch from integrated Lean main at
`888cbd8d7d68e7d1839cada300148f25d57b2b35`.
No edits to merged Track A proofs, `Kk.lean`, validation files, or protected manuscript prose.

## 1. Every numerical coordinate is a real copy or an odd dummy

For every height `k:Nat` and every `z:Nat`, exactly one of the following
holds:

* `z=2a+1` for some a (an odd dummy); or
* `z=iota_k(i,t)=2(k+1)i+2t`, where `t≤k` (a real copy).

The two cases are disjoint by parity. This is true also for k=0.
For the proof write `n=z/2`. The division algorithm yields
`z=2n+(z mod 2)`. If the remainder is 1, z is an odd dummy.
If it is 0, put `i=n/(k+1)`, `t=n mod (k+1)`. Since
`k+1>0`, the remainder is at most k, and
`n=(k+1)i+t`, so z is the desired actual hPosition. There is no
off-by-one gap or unrepresented even coordinate.

**Audit:** This classification applies to numbered numerical-H L
positions, *not* to full auxiliary H+ E incidence records. In
particular, odd vertices may have auxiliary E incidences even though
their ordinary binary L relation is always zero.

## 2. Exact all-future gap-zero lemma

Fix the actual original symmetric Boolean graph E, height k and finite
cutoff M. Let `m:Nat` be a *numerical* prefix endpoint, `G` a finite
subset of `[0,m)`, and `S` finite marked later **original** indices.
Assume `m≤iota_k(j,0)` for every j∈S: every marked original starts
strictly after the full prefix. Assume the **original** complete zero
certificate

```text
for every i,t with t≤k and iota_k(i,t)∈G,
for every j∈S, E(i,j)=false.
```

Then for every z∈G and every marked top position `w=iota_k(j,k)`,
the literal finite numerical H ordinary binary L has

```text
L(z,w)=L(w,z)=false.
```

**Proof.** If z is odd, apply the already verified
`hNumericBinary_odd_left_false` and
`hNumericBinary_odd_right_false`. If z=iota_k(i,t) with t≤k, then
`z<m≤iota_k(j,0)`. The existing `hPosition_before`, used with
generation 0 on the right, forces i<j (the equal-original
alternative would require t<0). The older-to-top exact equation gives
`L(z,w)=E(i,j)=false` for every t≤k; actual H symmetry gives the
reverse. This proof covers every unused numerical prefix coordinate:
no arbitrary numerical L-zero hypothesis survives.

**Audit:** The numerical m≤iota(j,0) guard is crucial. If only
m≤iota(j,k), the prefix may contain earlier-generation copies of
the *same* selected original; these have no original-edge column
E(i,j) for i<j, and the proof's strict-order step fails.
The lemma checks both directed arcs and all marked j, not one target.

## 3. Exact prefix partition (no lost vertices)

For arbitrary finite `P,Q⊆[0,m)`, define

```text
G = [0,m) \ (P ∪ Q).
```

Then `G⊆[0,m)` and `(P∪Q)∪G=[0,m)`. This is a literal finite
set equality, even if P and Q overlap; their disjointness may be
proved separately in the concrete physical application.
In the intended use Q is the complete ordered (possibly
nonconsecutive) reserved real-copy prefix and P contains all older
numerical coordinates. The existing
`orderedReservedNumericPrefix_inside_carrier` supplies Q⊆[0,m)
when `m=iota_k(q(a),g)+1`, and P⊆[0,m) is an explicit hypothesis.

For every selected original j after q(a), the checked block-order
lemma implies
`m=iota_k(q(a),g)+1 ≤ iota_k(j,0)` from q(a)<j and g≤k.
Therefore the gap-zero lemma applies to the exact set complement G,
once **original** zeros E(i,j)=0 are supplied for real copies i
whose coordinates lie in G.

This yields an exact *whole-prefix*, rather than merely a
displayed-pool, instance of the fully marked finite gluing theorem:

```text
K_ell-free_L([0,m) ∪ W)
  iff
K_ell-free_A(P∪W)
  and (if g<a then a else a+1) + cap_L(W_T) < ell.
```

Here W comprises actual marked top copies and the earlier Track A
typed support-column theorem provides reserved-to-W bits; the
remaining physical assumptions are complete old-reserve isolation,
safe past, reference L atoms and typed columns on P∪W, and
**only the original** real-gap zeros. This is per finite W and
does not assert one fixed list of actual future selected originals
realizes all abstract labelled graphs.

## 4. Adversarial checks and remaining geometric tasks

1. **No implicit partition of an arbitrary old past:** the exact
   complement G is used, so forgotten odd dummies and omitted
   original copies cannot vanish.
2. **Real vs dummy exhaustive:** modulo decomposition proves it at
   the numerical coordinate level, not by guessing a set of
   designated reserved generations.
3. **Future starts after cut:** all marked j satisfy the strict
   original ordering q(a)<j; replacing with a condition only on top
   coordinates is insufficient for the head-generation proof.
4. **Original zero condition needed:** gap originals between fresh
   q's may be linked to previously selected originals. The
   complete zero column toward every *new* marked future original
   must be supplied by Track B's stage schedule. It is not a
   consequence of the finite block being K-free.
5. **Gap odd vertices only ordinary L-zero:** the auxiliary E
   relation can be nontrivial and is handled in Track C.
6. **Internal W arbitrary:** reference table must allow every
   intended finite labelled clique/graph pattern. The actual
   edges between chosen top originals do not realize every
   possible W automatically.
7. **Safe entire past:** prefix K-free can be derived from actual
   numerical-H K-free semantics *if supplied*, or required as
   the complete finitePoolCliqueCheck certificate; do not infer
   it from the reserved clique-capacity formula alone.
8. **Nonconsecutive q:** use the merged
   `NonconsecutiveReservedPrefix` and
   `OrderedTopMarkedSupport` code, never relabel q(b) as N+b.
9. **Reference age:** these results establish exact physical
   reduction to the `P∪W` continuation test, not its equality
   with the integer graph age function F; a full reference
   profile identification still needs the independently
   verified all-support raw-bound equivalence.
10. **No global Ramsey claim:** neither unbounded schedule nor
    auxiliary Kpt E/B3/full-labelled orbit is provided.

## Actual finite-H carrier boundary

The finite numerical-H `L.binary` relation is defined on all Nat
coordinates even when its carrier is only `[0,M)`. The exact
whole-prefix age iff is consequently a Boolean-table theorem:
a **literal finite-H substructure** application also requires
`iota_k(q(a),g)<M` and `iota_k(j,k)<M` for every selected original
j. The new independent carrier lemma establishes membership of
every coordinate of `[0,iota_k(q(a),g)+1)∪W` from precisely those
guards. It prevents incorrectly claiming the L-table theorem by
itself places all future top names in the physical finite carrier.

## Lean contracts

A new `Kk/NumericPrefixGapZero.lean` will prove real-or-odd,
exact gap zeros, complete prefix partition, and future start
bound, then combine with the existing conditional ordered
top-front age theorem into a whole-prefix criterion.
Every hypothesis about actual original E-neighbourhoods stays
visible; no unverified physical existence is promoted.

Exact-head gates: explicit new module build, full `lake build`,
all exported theorem names under `#print axioms Kk....`,
strict standard-only transitive-axiom parser. Existing marker
and main aggregator edits reserved for the integration owner.
