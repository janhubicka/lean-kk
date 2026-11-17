# Track G — actual boring Kpt block factors through one monoid map

**17 November 2026, English proof and hostile audit written BEFORE Lean source.**

## Mathematical motivation and K4 regression

The verified G294/G298 one-node crossing-novelty interval theorem is NOT
the missing diary-uniform compression. Even when the unlabelled physical
crossing status is constant on an interval, that does not identify the
actual stage-dependent Kpt successor maps or the labelled inverse source.

The finite numerical-H K4 regression is **not** a boring interval:
`k4Gadget_algorithmRun_selects_cuts10_22` is already Lean verified.
For its real Kpt run containing the `x=38` original and scan height
`ell>22`, it gives
`10∈R.I 10` and `22∈R.I 22`. Thus any block containing 10
or 22 cannot satisfy the genuine "ALL levels boring" hypothesis,
although the selected x-only ordinary-L graph-age shadow may
remain unchanged at the first auxiliary clique stage. Do not
erase either q2 event. We record an exact corollary (using this
existing theorem) rather than duplicating the finite computation.

## Theorem 1 — honest finite boring-block factorization

Let `R` be ONE genuine `AlgorithmRun H X top` of
Algorithm 5.4 on an arbitrary successor-tree monoid.
Fix `low≤high≤top`. Assume for every `i` with
`low≤i<high` that the **actual** full parameter-closed
Kpt/abstract `SMTree.Envelope.IsInterestingAt` predicate
on `closure_(R.I(i+1))(X)` is FALSE.

Then
```
R.I low = R.I high,
∃ D : MMap H,  R.F low = MMap.comp H (R.F high) D.
```

In particular the REAL selected-level set is unchanged
throughout the block; the one accumulated D belongs to
the distinguished genuine Kpt monoid `M`.

**English proof:** descending induction on the finite interval
`i∈[low,high]`. Base `i=high`: selected-level equality is
reflexive and choose `D=MMap.id H` for the map factor.
At a genuinely boring cut `i` the checked
`R.noninteresting_step i` supplies a legitimate monoid
map `D_i` satisfying `D_i.map.SkipsOnly i`, the complete
actual Kpt predecessor crossing prescription on every
real pre-cut closure node, and
```
R.I i = R.I(i+1),
R.F i = MMap.comp H (R.F(i+1)) D_i.
```
The induction gives `R.I(i+1)=R.I high` and
`R.F(i+1)=MMap.comp H (R.F high) E`.
Taking `D=MMap.comp H E D_i` (composition belongs
to M by M1), associativity of the actual maps gives
`R.F i=MMap.comp H (R.F high) D`.
All equalities are genuine total `MMap H` equalities,
not merely equalities of graph-age projections or partial
maps on designated selected vertices.

The direct proof may use the same `Nat.strong_induction_on`
decreasing-stage pattern as existing `EnvelopeRun.lean`.
Do not assume an imported `MMap.comp_assoc` lemma:
`MMap.ext_apply` and definitional `MMap.comp_apply`
prove associativity on each genuine physical Kpt node.

This is a **finite block factorization** lemma, NOT a
collapse of the block's labels to one ordinary successor
letter. Its D is a potentially complicated composition
of all the individual boring-stage skipping maps.

## Theorem 2 — exact K4 obstacle to a shadow-inferred boring block

For the literal K4 gadget, take any genuine old run R on
Kpt seeds X containing actual x=38, scan top ell>22,
and any candidate block `low≤high≤ell` containing cut 10:
`low≤10<high`. Then it is **false** that EVERY cut in
`[low,high)` is genuinely boring for R. The same statement
holds with 22 in place of 10.

Proof: by the already-verified
`k4Gadget_algorithmRun_selects_cuts10_22`,
`10∈R.I 10` and `22∈R.I 22`.
If the cut were boring, the genuine
`R.noninteresting_step` would force
`R.I c = R.I(c+1)`. But every selected level in
`R.I(c+1)` is ≥c+1, by
`R.I_mem_bounds`. Contradiction. This requires
the genuine complete source test, NOT a user-supplied
age value or a new finite computation.

## Hostile audit: limits and false shortcuts

1. The hypothesis must be the actual full
   `IsInterestingAt H (closure S (R.I(i+1)) X) i`,
   not the absence of a graph-age change on a selected front.
2. The K4 fixture specifically falsifies inferred boringness
   at both q1=10 and q2=22 in every qualifying real run.
3. The accumulated factor `D` need not `SkipsOnly i` for
   ANY single i. A composition of several skip-only maps can
   skip multiple levels, even though it lies in the monoid M.
4. A factorization `F low=F high∘D` does not imply `D=id`.
   Individual boring steps can act nontrivially on full Kpt
   parameters, even while selected levels are unchanged.
5. The data `D_i` are existential choices from
   `noninteresting_step`; **uniqueness** of the aggregate D
   or its agreement across two independently realized diary
   occurrences is NOT proved.
6. The theorem applies to ONE actual AlgorithmRun, not
   simultaneously to arbitrary two runs. Common labels and
   inverse source orbits remain open.
7. At an interesting cut the map-update law is
   `F i=F(i+1)`, but the selected set ADDS cut i. Do not
   drop the every-cut boring hypothesis when claiming
   `R.I low=R.I high`.
8. `low=high` is the empty block; the identity factor
   works and the assertion is non-vacuous at boundaries.
9. `high=top` is allowed; no `noninteresting_step` is
   requested at top itself.
10. Associativity has to be proved for the actual
    `MMap H` type, including its monoid-membership proof
    fields. Pointwise extensionality handles proof irrelevance.
11. This does NOT imply that physical crossing
    `FullPhysicalClosureCrossing` is constant across the
    block. Its types live at varying coordinate lengths.
12. This does NOT transport the complete assigned upper
    dependent L+ labels over the entire block. The factor
    D records a total embedding, but it does not give a
    canonical finite event code for a refined diary.
13. This does NOT bound interval length, the number of
    physical bad cuts or the number of Kpt source nodes.
14. A single high-level new node may have missing old
    crossings at arbitrarily many genuinely boring cuts.
15. Corrected full B3 relative-continuation and independent
    infinite lower-bound unavoidability remain separate
    global proof obligations.
16. The exact K4 statement is a **necessary non-boring
    diagnosis**. It is NOT a counterexample to every possible
    refined diary expansion or to the published BRD counts.

## Lean acceptance

Formalize both items in an independent Kk module importing
the actual checked `SuccessorTree.EnvelopeRun` and
`Kk.K4ActualAlgorithmRunCut10` sources, with no new axioms
or `sorry`. Strict exact-head direct compilation,
`#check`/`#print axioms` of both statements and
the standard-only parser self-test must pass before adding
any blue manuscript validation mark.

The next research theorem after this would be a **uniform
boring-block inverse-label reconstruction** from the
complete Kpt stage data, not just existence of a factor D.
No such reconstruction theorem is claimed here.
