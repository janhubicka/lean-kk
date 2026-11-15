import Kk.FullOriginalInsertionAge
import Mathlib.Tactic

/-!
# Track B: exact raw old-column transport through an arbitrary map of sorts

English-first proof and adversarial checks:
docs/track_b_neutral_interval_sort_image_english_audit.md

Any map f : Fin d' → Fin d (including a noninjective map) pulls an
old-to-future column c back to c(p,f(t')). Every new common-old-
neighbourhood is EXACTLY the old common neighbourhood of the IMAGE
support. This preserves literal raw bounds at individual image supports.
It is NOT a general naturality theorem for canonical integer ages:
the two sort dimensions have different integer-weight spaces.

In particular, an all-support mutual capacity budget on the old
dimension transports to all supports of the pulled-back dimension,
and therefore certifies an age-NEUTRAL ordinary-original insertion
there. No Kpt parameter/source or diary orbit transport is asserted.
-/

namespace Kk

/-- Image of an admissible nonempty supported set under any sort map.
Noninjectivity is allowed; the image can only shrink cardinality. -/
def integerGraphSupportImage {d' d ell : Nat}
    (f : Fin d' → Fin d) (U : IntegerGraphSupport d' ell) :
    IntegerGraphSupport d ell := by
  classical
  refine ⟨U.1.image f, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := U.2.1
    exact ⟨f t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
  · exact (Finset.card_image_le).trans U.2.2

/-- The real original common-neighbourhood of pulled-back future
sorts equals the common-neighbourhood at the IMAGE of those sorts.
True for noninjective sort maps, all directed base graphs and every
finite old original pool. -/
theorem oldSupportCommonNeighbourPool_reindex
    {d' d : Nat} (P : Finset Nat)
    (c : Nat → Fin d → Bool) (f : Fin d' → Fin d)
    (U : Finset (Fin d')) :
    oldSupportCommonNeighbourPool P (fun p t => c p (f t)) U =
      oldSupportCommonNeighbourPool P c (U.image f) := by
  classical
  ext p
  simp only [oldSupportCommonNeighbourPool, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hAll⟩
    refine ⟨hp, ?_⟩
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact hAll s hs
  · rintro ⟨hp, hAll⟩
    refine ⟨hp, ?_⟩
    intro s hs
    exact hAll (f s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

/-- Exact RAW continuation-age identity under any future-sort map.
The output is evaluated at the image support; no global equality of
canonicalizers on different sort dimensions is asserted. -/
theorem finiteOldColumnRawBound_reindex
    {d' d ell : Nat} (E : Nat → Nat → Bool)
    (P : Finset Nat)
    (c : Nat → Fin d → Bool) (f : Fin d' → Fin d)
    (U : IntegerGraphSupport d' ell) :
    finiteOldColumnRawBound E ell d' P
        (fun p t => c p (f t)) U =
      finiteOldColumnRawBound E ell d P c
        (integerGraphSupportImage f U) := by
  change ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P (fun p t => c p (f t)) U.1) =
    ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c (U.1.image f))
  rw [oldSupportCommonNeighbourPool_reindex]

/-- Literal reindexing does not depend on whether the newly inserted
original has mixed links to reserved, selected, coding or gap originals.
The old pool and the enlarged pool both satisfy the same image law. -/
theorem finiteOldColumnRawBound_reindex_after_insert
    {d' d ell : Nat} (E : Nat → Nat → Bool)
    (P : Finset Nat) (v : Nat)
    (c : Nat → Fin d → Bool) (f : Fin d' → Fin d)
    (U : IntegerGraphSupport d' ell) :
    finiteOldColumnRawBound E ell d' (insert v P)
        (fun p t => c p (f t)) U =
      finiteOldColumnRawBound E ell d (insert v P) c
        (integerGraphSupportImage f U) :=
  finiteOldColumnRawBound_reindex E (insert v P) c f U

/-- A genuine complete future-sort mutual-neighbour budget transfers
from the larger sort domain to the image of an arbitrary smaller or
duplicated (noninjective) sort set. The source hypothesis is an
all-support budget: knowing it only for one chosen T is insufficient. -/
theorem original_mutual_budget_reindex
    {d' d ell : Nat} (E : Nat → Nat → Bool)
    (P : Finset Nat) (v : Nat)
    (c : Nat → Fin d → Bool) (f : Fin d' → Fin d)
    (hBudget : ∀ V : IntegerGraphSupport d ell,
      (∀ t ∈ V.1, c v t = true) →
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool P c V.1) v) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c V.1)) :
    ∀ U : IntegerGraphSupport d' ell,
      (∀ t ∈ U.1, c v (f t) = true) →
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool P
            (fun p t => c p (f t)) U.1) v) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P
          (fun p t => c p (f t)) U.1) := by
  classical
  intro U hLive
  have hImage :
      ∀ t ∈ (integerGraphSupportImage f U).1, c v t = true := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact hLive s hs
  have h := hBudget (integerGraphSupportImage f U) hImage
  simpa only [oldSupportCommonNeighbourPool_reindex] using h

/-- Conditional reindexed finite age-neutral insertion: the
ordinary raw/canonical age stays fixed within the PULLED BACK
sort dimension even though the actual source budget is stated on
the original sort dimension. This does not identify the TWO
canonical ages across dimensions. -/
theorem integerGraphAgeCanonical_next_prefix_neutral_reindex
    {d' d ell : Nat} (E : Nat → Nat → Bool)
    (b : Nat) (c : Nat → Fin d → Bool) (f : Fin d' → Fin d)
    (hBudget : ∀ V : IntegerGraphSupport d ell,
      (∀ t ∈ V.1, c b t = true) →
      1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool (Finset.range b) c V.1) b) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c V.1)) :
    integerGraphAgeCanonical d' ell
        (finiteOldColumnRawBound E ell d' (Finset.range (b+1))
          (fun p t => c p (f t))) =
      integerGraphAgeCanonical d' ell
        (finiteOldColumnRawBound E ell d' (Finset.range b)
          (fun p t => c p (f t))) := by
  exact integerGraphAgeCanonical_next_prefix_eq_of_mutual_budgets
    E ell d' b (fun p t => c p (f t))
      (original_mutual_budget_reindex E (Finset.range b) b c f hBudget)

#print axioms Kk.integerGraphSupportImage
#print axioms Kk.oldSupportCommonNeighbourPool_reindex
#print axioms Kk.finiteOldColumnRawBound_reindex
#print axioms Kk.finiteOldColumnRawBound_reindex_after_insert
#print axioms Kk.original_mutual_budget_reindex
#print axioms Kk.integerGraphAgeCanonical_next_prefix_neutral_reindex

end Kk
