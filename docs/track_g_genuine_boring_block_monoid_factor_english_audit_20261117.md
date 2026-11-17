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

## Stronger adversarial theorem: every genuinely boring cut changes F

This is the correct mathematical warning against mistaking a
boring block for **equality of total Kpt monoid maps**.

For a real AlgorithmRun R at top t and cut i<t, write
`Z_i=closure_(R.I(i+1))(X)`. If the genuine full
`IsInterestingAt(H,Z_i,i)` is FALSE, the actual recursion
supplies a skip-only map D_i with

```
R.F i = MMap.comp H (R.F (i+1)) D_i,
D_i.map.SkipsOnly i.
```

**Theorem:** `R.F i ≠ R.F(i+1)`.
For suppose equality held. For each tree node x, we
would have
`R.F(i+1)(D_i x)=R.F(i+1)(x)`. Since the genuine
`ShapeMap` underlying `R.F(i+1)` is injective,
`D_i x=x` for EVERY x. But `H.level_nonempty i`
supplies a genuine Kpt node x of level i. Then
`D_i x=x` puts i in `D_i.map.levelRange`,
contradicting `D_i.map.SkipsOnly i`.

Conversely at a genuinely **interesting** cut the
recorded step law gives `R.F i=R.F(i+1)`.
Therefore we have the **exact one-stage classification**

```
R.F i = R.F(i+1)
   iff IsInterestingAt(H, closure_(R.I(i+1))(X), i).
```

Notice the polarity: **boring** ⇒ `I` unchanged and
`F` changed; **interesting** ⇒ `I` adds the cut and
`F` unchanged. This is a consequence of the actual
Algorithm 5.4 step laws plus M-map injectivity, not an
assumption about numerical-H source geometry.

The previously proposed finite boring-block factorization
remains correct but is much weaker as a *compression*
principle than its name might suggest. Indeed the existence
of some accumulated factor `D` would hold over **every**
finite AlgorithmRun block, by using identity factors at
interesting steps and the recorded skip-only factors at
boring steps. The genuinely boring-block-specific conclusion
is the equality of the SELECTED `I` sets. The composite
`D` can remember arbitrarily much stage information and
cannot simply be erased. A true source-label compression
must compare the ASSIGNED full Kpt monoid maps or their
restriction to the relevant finite labelled inverse
carriers, not only the selected levels or an aggregate
factorization. We explicitly reject "boring ⇒ F unchanged".

The K4 actual cuts 10 and 22 are interesting, so there
the total F map remains equal across the stage while the
I-set changes. This consistent polarity makes the genuine
K4 fixture an essential regression for the classifier.

**Additional hostile checks:**
- M2/M3 tree nonemptiness is used via `SMTree.level_nonempty`;
  without a level-i node, skip-only might not prove a
  pointwise map change at that coordinate.
- The injectivity argument is for the TOTAL shape map
  `(R.F (i+1)).map`, not an ordinary-L graph-age quotient.
- If the cut is interesting then F equality follows
  definitionally from the actual run, but it does not
  imply a complete match of physical source labels
  between two unrelated occurrences.
- The exact iff is for a SINGLE genuine run at a fixed
  cut `i<t`, and does not certify a global unbounded
  Kpt diary source orbit.

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
5. The data `D_i` are existential witnesses from
   `noninteresting_step`. For a FIXED run R and fixed endpoints
   low/high, the aggregate D is nevertheless UNIQUE: if
   `F low = F high ∘ D = F high ∘ D'`, injectivity of `F high`
   gives `D x = D' x` for every node x, and MMap extensionality
   gives `D = D'`. This cancellation does NOT establish a
   canonical choice or equality across different runs or diary
   occurrences, or any bound on the factor's complexity or labels.
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

Formalize all four endpoints in an independent Kk module importing
the actual checked `SuccessorTree.EnvelopeRun` and
`Kk.K4ActualAlgorithmRunCut10` sources, with no new axioms
or `sorry`. Strict exact-head direct compilation,
`#check`/`#print axioms` of all four statements and
the standard-only parser self-test must pass before adding
any blue manuscript validation mark.

The next research theorem after this would be a **uniform
boring-block inverse-label reconstruction** from the
complete Kpt stage data, not just existence of a factor D.
No such reconstruction theorem is claimed here.
