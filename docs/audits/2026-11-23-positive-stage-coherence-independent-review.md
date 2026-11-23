# Independent review: bounded positive-generation stage coherence

Reviewed before Lean implementation on 23 November 2026 by the manuscript
review agent, independently of the author of the proposed lemma.

Reviewed English source:
`docs/positive_generation_stage_coherence_english_20261123.md`

SHA256:
`3f9c7dbd8078fcf82b0cf96432e92e5a25bed3d4710caf8b8ed289271b34f5ad`

## Verdict

Approved for implementation. This is an English proof review, not a kernel
validation claim or an approval of the full upper characterisation.

The original unbounded address contracts were an application blocker. The
revised contracts explicitly require `m ≤ k`, matching the actual physical
generations and the bound supplied by the positive-neighbour decoder. The
revision resolves that blocker without assuming the desired coherence result.

## Checks against current source

1. `hPosition k j m = 2*(k+1)*j + 2*m` has noncanonical aliases for
   unbounded `m`. The numerical examples in the revised English note are
   correct. Bounded injectivity is exactly the relevant uniqueness statement.
2. Membership of `hOriginalName Stage v` in the literal `hStageOriginals`
   supplies either root membership or membership in `J` with positive free
   level. The bounded root and Plan contracts therefore give the proposed
   bounded stage-name classification when `m ≤ k` is supplied.
3. The existing ordinary-base classification eliminates dummy and auxiliary
   target roles from an actual positive base edge out of an omitted base.
   Combining it with the bounded stage classification forces `m = k`.
4. `q = hPosition k b 0 ≤ hPosition k b g = c`. Thus `c < N` gives `q < N`,
   and `c+1 ≤ freeLevel` gives `q+1 ≤ freeLevel`. Eligibility at q is derived,
   not an extra hypothesis or an inference from numeric order alone.
5. At either positive coordinate, the physical-neighbour theorem supplies a
   later base, a bounded generation and the exact address. Applying the
   bounded role helper in both directions is essential: positivity at q alone
   only initially forces `0 < m`, not `g < m`.
6. Once `m = k`, `hNumericBinary_real_forward_iff` gives both gates because
   `0 < k` and `g < k`. Equivalence of Boolean positivity gives literal bit
   equality, including the false case and names with no positive real edge.
7. `0 < g` gives `q < c`. The proposed extraction of the old q-bit uses the
   exact existing `finiteOldFullTypes_ne_of_distinguishing_L_bit` pattern:
   apply `PartialTypeWithE.lReduct`, identify both reducts, and evaluate
   binary at `(some ⟨q,q<c⟩, none, 0)`.
8. `hQ.sym` supplies the symmetry required by the restored
   `full_equal_ordinary_cut_column_determines_next_type`. Its actual
   `Fin A.size` originals are the stage names, and its two eligibility
   premises and complete old-type equality are exactly available.
9. The first endpoint allows `g = 0` only as a tautological column equality.
   Complete next-type coherence uses `0 < g`; no generation-zero separation
   claim is obtained by treating q as old when q equals c.
10. The proof does not use canonical-age equality, block intervals, selected
    no-split, a marked terminal subtuple, or no-I1/no-I2 as a premise.

## Application boundaries retained

The result remains conditional on the actual descending stage inclusion,
bounded root/Plan role contracts and chronological base axioms. It does not
construct those data, establish all generation-zero cases, lift through every
closure representation to no-I1/no-I2, verify corrected B3, or establish the
common labelled source orbit. The old unbounded selected-coded skip theorem
must not be presented as an instantiated theorem of the intended Q source.
