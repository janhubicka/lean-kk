# Track G — uniqueness of the actual boring-block monoid factor

**17 November 2026, English-first proof and adversarial audit before Lean.**

## Correction discovered by postmerge adversarial audit

Merged Track G #305 proves that if every cut in a finite block
`low≤i<high` is genuinely boring for ONE actual AlgorithmRun, then
its selected I-level sets agree at low and high and there EXISTS
a legitimate total Kpt monoid factor D with
`R.F(low)=MMap.comp H (R.F(high)) D`.

That factor is in fact **UNIQUE for the given endpoint total maps**.
An early English review was too pessimistic about uniqueness.
The main G305 audit has already been corrected to distinguish
within-run factor uniqueness from the still missing **agreement of
endpoint maps across distinct diary occurrences**. This note
records the short proof as its own kernel-checkable endpoint.

## Lemma U1 — left-cancellation for genuine MMaps

Fix an arbitrary `SMTree S` with distinguished monoid
`M`, and `F,D,E : MMap H`. Suppose

```
MMap.comp H F D = MMap.comp H F E.
```

Then `D=E`.

**Full proof.** Evaluate the equality at any genuine
tree node x. By the actual `MMap.comp_apply` definition,

```
F (D x) = F (E x).
```

The underlying `ShapeMap` of F is injective by the
successor-tree structural interface, so `D x=E x`.
Extensionality `MMap.ext_apply` over all nodes gives
`D=E`. The monoid-membership proof components are
irrelevant by `MMap.ext_map`. No cancellation on the RIGHT
is assumed or proved.

This is general; it does NOT require a boring cut or a
particular finite diary. The actual hypotheses are the
**total** MMap equality, not only equality on a finite
subfamily of marked selected vertices or their L-reducts.

## Lemma U2 — unique finite boring-block factor

Let `R : AlgorithmRun H X top`, `low≤high≤top`,
and assume every actual full parameter-closed stage
`i∈[low,high)` is genuinely boring. By the verified
G305 theorem, there exists some D with

`R.I(low)=R.I(high)`,
`R.F(low)=MMap.comp H (R.F(high)) D`.

If any two such D,E witness that equation, U1 cancels
the injective outer map `R.F(high)`, so D=E.
Therefore there is **exactly one** such total
factor `D : MMap H`. No extra finite-index
bijection, no canonical selection from individual
boring-stage skip maps and no MMap associativity
axiom beyond the verified definition are needed.

## Cross-occurrence boundary

The factor is unique *once the actual endpoint total
maps are fixed*. In two different diary occurrences,
their Kpt monoid endpoint embeddings may differ,
their numerical source cuts may differ, and even
the labelled parameter carriers may not yet have
a coherent identification. Hence U2 does **not**
establish equality of the two factors or a common
labelled inverse-source orbit.

A corresponding **conditional** two-run statement
would be immediate if both endpoint total maps
were already identified under an appropriate Kpt
source comparison. But equality of those total maps
is at least as demanding as the missing labelled
transport problem and is **not** available merely
from equality of abstract macrodiaries.

## Hostile checks

1. Left-cancellation uses F injective, so cannot be
   applied to a graph-age quotient or a partial
   map whose values on unmarked Kpt parameters are
   unspecified.
2. It is left-cancellation, not right-cancellation:
   `D∘F=E∘F` need not imply D=E if F is not surjective.
3. The result proves equality as **total MMap H**,
   not merely level maps or projected selected ages.
4. No uniqueness of the chosen witnesses D_i from
   each `noninteresting_step` is needed for U2,
   though it follows by the same left-cancellation
   argument.
5. The unique aggregate D need not be the identity
   or skip only one cut. Its actual total action
   can encode an arbitrarily long boring block.
6. The *existence* of a factor follows from merged
   G305 only under genuine full-source boringness.
   K4 auxiliary cuts 10 and 22 violate that
   hypothesis for the seeded numerical-H gadget.
7. The uniqueness part is independent of any K4
   geometry and holds for arbitrary successor
   trees with injective shape maps.
8. A unique D for one run is not a common D
   across different realised occurrences.
9. Nothing proves a **uniform finite code** or
   bound for D independent of scan height.
10. The labelled-source monoid orbit, full corrected
    B3 relative-continuation and independent
    infinite lower colouring remain open.
11. All 12 global manuscript PENDING claims remain
    pending; adding this statement can justify only
    a scoped BLUE interface after direct Lean CI.
12. Do not modify the manuscript's frozen black
    sections or infer published BRD numbers.

## Lean acceptance

Import the exact merged G305 module and prove generic
`MMap` left cancellation, then its actual-run
unique-factor corollary in a new standalone file.
Run dedicated exact-head compilation, strict parser
negative self-test and two registered transitive-axiom
reports. The ordinary full-repo build alone is
not proof of the standalone module unless imported.
