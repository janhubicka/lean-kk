# Track D — failed selected-stage B3 forces a non-top real numerical generation

15 November 2026 — English proof and adversarial audit **before Lean**.

## Motivation

The earlier Track D odd-cut reduction handles dummy physical coordinates,
but it leaves a stronger unused fact in the successor-tree relocation
theorem `numericI3_actual_witness_generation_conclusions`: for an
irreducible forbidden witness on a true numerical H, its *last lower*
vertex (the tested cut) occurs at real generation `r-1`, where
`1 <= r <= k` is the number of old vertices in that witness.
Therefore, on any failed selected-stage full corrected B3 test,
the tested cut has real generation `g=r-1<k`.
This is **not** an assumption of the selected-stage theorem; it follows
from actual Henson forbidden-clique geometry and complete chosen
upper ordinary-L types.

The existing `Kk/HensonAnyGenerationHigherSignature.lean` assumes
a known real cut `cut=hPosition k idx g` with `g<k`
before proving that a failed B3 witness has upper names at higher
generations. The present lemma **derives** the non-top hypothesis
directly from B3 failure. It is not just the trivial generation-gate
observation, because top-to-top numeric H edges are permitted by the
special `q=m=k` clause.

## Exact theorem and proof

Fix ell>=2, ell<=k+1, symmetric loop-free K_ell-free base E,
finite numerical H carrier N, actual cut `c<N`, arbitrary finite
original list `original : Fin M -> Fin N`, arbitrary selected-name
predicate `Selected : Fin M -> Prop`. Suppose that the TRUE
`selectedStagePoolPrescribedData` at c fails corrected B3.

**Claim:** there exist natural numbers i,g with `g<k` and
`c=hPosition k i g`.

1. The checked
   `henson_selectedB3_failure_has_clique_witness` constructs an
   ordinary-L finite age-test model W, the actual initial ordinary-L
   socle of numerical H through c, actual chosen eligible source names
   for **every upper vertex**, deletion avoidance for the full normalized
   family, and one forbidden clique `K_ell`. No auxiliary E is added to W.
2. The normalized `K_ell` pattern is irreducible, has size `ell<=k+1`,
   and the actual finite numerical H is K_ell-free. Apply
   `normalizedForbidden_bounded_signature_cut` to this specific W.
   It gives the actual clique embedding e, a proper cut rank r with
   `0<r<ell` and **`r<=k`**, and the final old clique coordinate
   e(r-1)=c. The entire forbidden clique after deleting c is absent.
3. For each upper clique vertex e(b), b>=r, the checked selected-stage
   witness gives **one genuine selected original v** whose
   complete (c+1) directed ordinary-L type equals the W type and whose
   actual free E cut satisfies `c+1 <= freeLevel(original(v))`.
   The checked ambient axiom `freeLevel(v)<=v` therefore implies
   `c<original(v)`; this is the *actual numeric original address*,
   not an abstract diary type.
4. Forget only the source name, retaining its complete (c+1) ordinary-L
   equality, its actual physical address and `c<address`.
   Apply the already checked **whole-forbidden-copy relocation**
   theorem `numericI3_actual_witness_generation_conclusions`,
   with the SAME W, e and r. It proves
   `c = hPosition k i (r-1)`. The theorem's proof uses the
   complete H ordinary-L source/upper atoms and the actual
   forbidden-free old socle to exclude the exceptional top tie.
5. Set `g=r-1`. Since `0<r<=k`, `g<k`.
   Hence the exact finite source cut has a real **non-top**
   generation. No physical source-matching or no-(I2) hypothesis is
   used anywhere in this consequence.

**Corollary:** for any fixed real **top** cut `c=hPosition k i k<N`,
the selected-stage full corrected B3 test passes for any selected
original pool. If it failed, the theorem would also represent c as
`hPosition k j g` with `g<k`. The independently verified
`hPosition_injective_bounded` says `k=g`, contradiction.

Together with the independently audited odd-cut statement, this
restricts possible finite corrected B3 failures to **even real
non-top-generation** cuts. It leaves true I1/I2 events untouched.

## Hostile checks

1. No application of the positive-generation theorem to generation
   zero; use `henson_selectedB3_failure_has_clique_witness`, which
   includes zero by correctly excluding singleton and asymmetric patterns.
2. The culprit is specifically an actual K_ell clique. Arbitrary
   normalized forbidden families can fail for singleton or asymmetric
   relational reasons without any strict-generation conclusion.
3. The numerical H base E is explicitly loop-free/symmetric/K_ell-free.
   Neither E2/E3 nor an arbitrary H+ extension implies this alone.
4. The numeric parameter `k` is the height-`k` generator and
   satisfies `ell<=k+1`. Do not confuse it with a graph parameter
   indexing K_k-free graphs in another convention.
5. The upper labels are **complete directed (c+1) ordinary-L types**,
   including negative atoms, and are actually selected *eligible*
   original addresses (not merely equal old source L+ masks).
6. The `freeLevel <= index` and `c+1 <= freeLevel` steps are vital:
   relocation requires an original address **after** c, not just a
   future vertex of the auxiliary W with an arbitrary named type.
7. r is the number of lower vertices of the forbidden **clique**
   and satisfies `0<r<=k`; `r<ell` alone would not give
   `r<=k` if one omitted `ell<=k+1`.
8. Same initial-L old socle is essential for the relocation
   contradiction. Equality of selected-front graph-age capacities
   alone is NOT enough.
9. Do not infer the result just from the bare H gate: the exceptional
   allowed top-top pair `q=m=k` would invalidate that shortcut.
   The full forbidden-clique relocation is the needed stronger input.
10. No auxiliary E structure is put on W; real free-level cut checks
    are performed only on actual numerical-H originals.
11. The conclusion does NOT identify any upper original as a selected
    diary branch; it may be a genuinely auxiliary closure parameter.
12. No no-(I2) premise is needed to obtain the generation location.
    It will be needed later for chosen-source fibre comparisons.
13. This is a theorem for *any* finite selected-source predicate,
    including an empty predicate (in which case failure is impossible).
14. The top-cut corollary does not assert top cuts are universally
    boring: the retained top coding levels can still be structural
    (I1)/(I2) events.
15. Combine with odd fake cuts only after each exact-head kernel
    gate has succeeded; do not write a GREEN manuscript mark
    based on this English argument alone.
16. The general small-independent bounded full-source proof still
    must classify all **non-top real omitted** cut neighbours,
    prove marked chosen-output B3 and rule out full-source I1/I2.
17. The user-supplied diary counts and the existing lower bound
    are independent of this finite theorem; it cannot prove a
    copy-degree characterization or labelled inverse source orbit.
18. Check the exact LEAN signature and transitive axiom print on
    the new theorem; do not rely on CI from another source head.

## Proposed Lean module

`Kk/B3FailedCutGeneration.lean`: import
`Kk.HensonZeroGenerationClique` and
`SuccessorTree.V10.I3ActualWitnessGeneration`.
Construct the complete finite witness as in
`Kk.HensonAnyGenerationHigherSignature`, but **without**
any `hg : g<k` or `hGeneration` assumptions.
After `numericI3_actual_witness_generation_conclusions`,
return `⟨r-1,i,by omega,hGen⟩`.
Derive top-cut impossibility using `hPosition_injective_bounded`.
Register both exact named theorems in the strict standard-only
axiom report. This does not modify or import the unverified global
small-independent application.

## Further packaged corollary — one same-core higher-generation witness

Once the non-top real cut `c=hPosition k idx g`, `g<k`, is
**derived** rather than assumed, apply the already verified
`henson_any_generation_B3_has_clique_higher_signature` at this
same cut, same selected name pool and same failed corrected B3.
It returns **one** genuine finite ordinary-L forbidden `K_ell`
signature witness, with every upper vertex represented by
an actual selected original of some generation `m>g`.
Importantly, the theorem supplies one shared forbidden clique
rather than collecting unrelated individual positive neighbours.

This is a direct composition of two existing / newly formalized
finite theorems; it is not a new graph-age/diary bridge.
The complete selected upper-type equality and the finite original
name map are retained. The failure implies `g<k` but does not
identify the higher names with active diary branches, which can still
omit genuine auxiliary parameters.

Additional adversarial checks: use the same original map and
`Selected` on both invocations, preserve exactly the same
`cut` and `hFailure` witness, and do not move `g<k` into an
external hypothesis. Do not weaken next-cut L-type equality to
one positive adjacency bit. Register an additional exact named
transitive-axiom report only after the new corollary compiles.
