# Track C — cross-carrier stability of the TRUE full parameter-closed source and corrected B3

**14 November 2026 — English mathematical proof and adversarial review BEFORE Lean.**
This is stacked on [PR #140](https://github.com/janhubicka/lean-kk/pull/140): physical fixed-generation numerical-H+ old E / complete L+ prefix coherence.

## Exact statement C32

Fix the base age model `K`, generation parameter `k`, bounds `N≤M`,
a normalized forbidden family `family`, and real forbidden-avoidance
proofs for both A_N=finiteNumericH K k N and A_M=finiteNumericH K k M.
Fix **one and the same actual Kpt seed set** `X`, original-name
pool `U⊆Fin N` satisfying `X⊆ambientPrefixPool family A_N U`,
selected-level set `I⊆Nat`, and cut `p`.

The complete physical Kpt closure
`Z=Envelope.closure (admissibleKptSTree family) I X`
is a literal set of `AdmissibleKptNode family` and does not change
when an older finite representation A_N is extended to A_M:
the *same* source X and I are used, and the Kpt tree itself is
determined by the fixed forbidden family.

The new physical-prefix theorem transports the old actual seed
prefix pool into A_M, including its E, free cut, complete L+ and
original Kpt values.

Let `id_N : Fin N→Fin N` and `id_M : Fin M→Fin M` be the
FULL ORIGINAL carrier enumerations, not marked-selected shadows.
Define `F_N = closureSelectedBoringData family A_N hAvoidN id_N Z p`,
and `F_M` analogously for A_M.

Assume there is NO competing exact (I2) cut-level meet in the
ENTIRE Z, i.e. `¬∃a,b∈Z, SameComponent(a,b)∧lev(meet a b)=p`.

Then
- `F_N.source = F_M.source` (both source sets are complete dependent L+ types);
- for every `T∈F_N.source`, `F_N.target T = F_M.target T` (entire assigned upper L+ type, including E and negative L atoms);
- `F_N.CorrectedB3 family ↔ F_M.CorrectedB3 family` (the genuine full L-age obstruction verdict is unchanged).

## English proof (non-circular)

1. The verified `admissibleKpt_stage_closure_subset_pool` applied to
A_N, U, I, X gives every actual `z∈Z` one genuine old numerical-H
original v∈Fin N with `z≤A_N.kptOriginal v`; the entire
meet-and-parameter closure, not a selected subset, is represented.
2. By PR #140's exact OLD Kpt original equality and seed-pool-lift
lemma, `X⊆ambientPrefixPool family A_M (Fin.castLE '' U)`.
The SAME verified full closure invariant gives each z∈Z a
genuine new ambient witness `w∈Fin M`, possibly one of the newly
added parameters. This proves both *actual pool* hypotheses required
by Track E's already kernel-checked cross-presentation comparison.
3. The physical relation `FullPhysicalClosureCrossing family Z p`
is defined solely from the actual Kpt nodes z and their dependent
ancestors, so on the two sides it is **literally identical** (`rfl`).
No arbitrary E or selected-front graph-age projection is introduced.
4. Apply the already verified
`two_numericH_closures_B3_of_equal_full_crossing_relation`
with both Z arguments the same literal Z and both original-name
functions the identity. This theorem uses exact coverage+graph of
the full closure at no-(I2) cuts to derive the source equality,
complete assigned upper-type equality *on the source*, and corrected
B3 equivalence.

No rewriting or identification of `F_N.target T` outside its
partial source is justified; those values are arbitrary and are
NOT compared.

## C33: named old-source membership survives growth WITHOUT no-(I2)

Fix any finite old name index `original : Fin P→Fin N`,
`Z:Set AdmissibleKptNode family`, and cut p. For v∈Fin P,
`closureSelectedOriginal family A_N hAvoidN original Z p v`
iff the same selected predicate holds in A_M with the
name `Fin.castLE∘original`. This is an even stronger exact source
identity than B3-stability but does **not** assert equality of a
prescribed map's chosen next target at an I2 fork. The proof just
unpacks `closureSelectedOriginal` and replaces the Kpt original by
the literally E/L+-equal one from PR #140.

## Hostile checks

1. The base K and generation k are FIXED; if k changes, numerical H
   coordinates, binary generation gates and E columns change.
2. The seed set X and the selected-level set I are literally SAME
   on both sides. Newly inserted resolved-copy seeds must first be
   separately represented; we do not prove their closure stays equal.
3. hAvoidN and hAvoidM concern the REAL finite H+ L reducts, not
   an invented labelled expansion on a finite B3 witness.
4. A full `Fin N`/ `Fin M` original-name enumeration is required
   for the explicit F_N/F_M stated here. A selected-shadow pool
   need not cover all Z and does NOT suffice.
5. Even though the larger ambient offers more original witnesses,
   any extra old/upper pair from a Z-node is already represented
   by the smaller model's genuine full crossing coverage.
6. No-(I2) is indispensable for a SINGLE-VALUED prescribed F
   covering every crossing. At I2 cuts compare the physical
   **relation**, not a chosen F target function.
7. Equality of target functions is asserted only for T in source,
   not at arbitrary total dummy values outside source.
8. Corrected B3 is the *ordinary L-only age test* applied to
   the complete physical prescribed source; E is never added to
   its abstract finite forbidden-extension witness.
9. Every actual odd fake E-predecessor coordinate of an old target
   remains present in its complete partial type under growing N.
10. For cuts past N the statements remain valid only because Z's
    crossing nodes are still controlled by old original free cuts;
    do not infer a general `partialTypeAt` equality beyond N.
11. The named old-source iff holds at I2 cuts, but equality of a
    chosen next F target there is intentionally not claimed.
12. Full closure membership is set membership in a real Kpt
    successor tree; it is not a set of arbitrary meet recipes
    with potentially different representatives.
13. The current result is within one fixed Kpt closure Z; it does
    NOT match closures of two different macrodiary occurrences.
14. It does not supply the Henson forbidden-clique column
    certificates needed to introduce NEW reserved originals.
15. The actual K4 cuts 10 and 22 are still potentially interesting;
    no projection to selected-front age or claim of boringness.
16. No uniform source index/cardinality bound, shared labelled
    inverse orbit, or unconditional BRD characterization follows.

Lean targets: `Kk/NumericHPrefixB3Stability.lean` and two
exact named endpoints; isolated standard-only axiom gate plus
full project build. Leave all central imports, manuscript black
and olive text and validation marks to Track G.
