# Track D — all odd numerical-H cuts are corrected-(B3) good
15 November 2026. English-first proof and adversarial audit.

## Statement

Let ell>=2, ell<=k+1, E:N x N -> Bool be symmetric, loop-free,
and K_ell-free. Let A be the actual finite numerical-H model over E
of carrier N and generation height k. Fix an odd tested cut
c=2a+1<N, any finite original map Fin M -> Fin N, and any Full
predicate on those originals.

**Claim:** the ACTUAL selected-stage prescribed function on this
Full pool passes corrected (B3) for the Henson K_ell forbidden family,
with no no-(I2) hypothesis, no source nonemptiness, and no assumption
on the selected original pool.

## English proof

Suppose corrected (B3) fails. The already checked theorem
`henson_failedSelectedB3_has_eligible_cut_neighbour`
in `Kk/B3CutStarNormalForm.lean` produces a genuinely Full,
cut-eligible physical original v with an actual positive
ordinary-L crossing atom L(c,original(v))=true.
However the literal numerical H ordinary-L definition gives
`hNumericBinary_odd_left_false` at c=2a+1, for every target
original index and every binary relation symbol. Thus
L(c,original(v))=false, contradiction.

No interpolation of graph-age capacities and no chosen-output
source matching is needed: odd dummy coordinates simply have
no positive ordinary-L crossings at all.

## Hostile audit

1. The hypothesis is the *physical* numerical coordinate c=2a+1,
   not an ordinal labelled `odd` in an arbitrary compressed source.
2. The cut is within the genuine finite model, c<N.
3. The normalized forbidden family must be that of undirected
   K_ell-free graphs, since the physical cut-neighbour extraction
   is false for arbitrary forbidden relational patterns.
4. Loop-free, symmetry and K_ell-freeness of E are retained as
   hypotheses of the existing extraction theorem. They do not
   follow from oddness alone.
5. The ordinary binary L at the odd physical cut is false even
   though the auxiliary numerical H+ E can have positive atoms.
6. Therefore this proves ONLY the B3 test, NOT absence of
   (I1) endpoints or (I2) competing meets at odd levels.
7. In fact genuine positive free cuts of retained parameters often
   are odd and intentionally MUST be retained for (I1).
8. Nothing here establishes that a given even real level can be
   skipped. Odd-cut B3 alone is insufficient for the global
   small-independent full-boringness lemma.
9. The original pool can be empty or arbitrary; no marked-source
   nonempty assumption is hidden.
10. The proof does not introduce E on arbitrary ordinary-L
    B3 witness vertices; it only reads the actual physical
    L(c,original(v)) atom forced by failed corrected B3.
11. Do not extrapolate from physical odd parity to an arbitrary
    normalised monoid source after level compression: use the
    actual fixed numerical H coordinate before reindexing.
12. Strict named Lean axiom registration is required before
    adding a paper GREEN mark. Manuscript applications remain
    conditional on genuine source/run compatibility.

## Implementation plan

Add `Kk/B3OddFakeCut.lean` importing the checked exact
physical cut-neighbour extraction. Prove by contradiction:
failure -> positive eligible original v, then rewrite its
actual L crossing by the checked
`hNumericBinary_odd_left_false`. No use of no-(I2).
Test with a dedicated exact-head build and standard-axiom gate.

This is an actual finite source theorem and a concrete
proved (B3) subcase of the small-independent proof target,
not an unconditional global full-boringness assertion.
