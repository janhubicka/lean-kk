import Kk.TrackFCoverEssentialSupport
import Kk.TrackFCoverOneStep
import Kk.IntegerAgeLocality
import Mathlib.Tactic

/-!
# Track F: complete graph-age cover support-value classification

For a genuine finite K_ell integer-witness graph-age cover F' ⋖ F:
  (1) each changed coordinate drops exactly one (TrackFCoverOneStep);
  (2) there is exactly one inclusion-minimal changed support T
      (TrackFCoverEssentialSupport);
  (3) EVERY changed support U satisfies F(U)=F(T).

The new proof of (3) uses the already verified single-support
canonicalization locality theorem, rather than a second complicated
integer-witness argument. All hypotheses of that theorem are discharged
for the actual finite K_ell age, and not for arbitrary noncanonical
raw bounds. This module does not prove splitting, coding E, diary
inverse, source B3, or independent infinite big Ramsey lower bounds.
-/

namespace Kk

/-- Lowering one RAW support bound at any changed support U of a
genuine cover produces exactly the lower canonical graph age. -/
theorem trackFCover_single_support_canonical
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (U : IntegerGraphSupport d ell)
    (hUChanged : lower U < upper U) :
    integerGraphAgeCanonical d ell
      (integerAgeLowerAt d ell upper U (lower U)) = lower := by
  classical
  let B := integerAgeLowerAt d ell upper U (lower U)
  have hLowerB : AgeLe lower B := by
    intro V
    by_cases hVU : V = U
    · subst V
      simpa [B, integerAgeLowerAt] using
        (le_min (hCover.le U) (le_refl (lower U)))
    · simpa [B, integerAgeLowerAt, hVU] using hCover.le V
  have hGage : IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell B) :=
    integerGraphAgeCanonical_is_age d ell B lower
      hCover.lower_age hLowerB
  have hLowerG : AgeLe lower (integerGraphAgeCanonical d ell B) :=
    integerGraphAgeCanonical_greatest d ell B lower
      hCover.lower_age hLowerB
  have hGUpper : AgeLe (integerGraphAgeCanonical d ell B) upper := by
    intro V
    exact (integerGraphAgeCanonical_le_raw d ell B V).trans
      (integerAgeLowerAt_le d ell upper U (lower U) V)
  have hNotUpper : integerGraphAgeCanonical d ell B ≠ upper := by
    intro hEq
    have hBound : upper U ≤ B U := by
      simpa only [hEq] using
        (integerGraphAgeCanonical_le_raw d ell B U)
    have hBU : B U ≤ lower U := by
      simpa [B, integerAgeLowerAt] using
        (Nat.min_le_right (upper U) (lower U))
    omega
  rcases hCover.no_intermediate (integerGraphAgeCanonical d ell B)
      hGage hLowerG hGUpper with h | h
  · exact h
  · exact False.elim (hNotUpper h)

/-- With T contained in a changed support U, the already verified
one-support locality lemma and exact one-step cover drop force
equal upper ages F(T)=F(U). This sublemma does not require T minimal,
only that T itself changes and lies in U. -/
theorem trackFCover_changed_values_of_containment
    (d ell : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (T U : IntegerGraphSupport d ell)
    (hTChanged : lower T < upper T)
    (hUChanged : lower U < upper U)
    (hTU : T.1 ⊆ U.1)
    (hUStep : upper U = lower U + 1) :
    upper T = upper U := by
  have hMonTU : upper T ≤ upper U :=
    integerGraphAge_monotone d ell upper hCover.upper_age T U hTU
  by_contra hNe
  have hTLe : upper T ≤ lower U := by omega
  have hOverlap : ∀ V : IntegerGraphSupport d ell,
      V.1 ⊆ U.1 → V.1 ⊆ T.1 → upper V ≤ lower U := by
    intro V _ hVT
    exact (integerGraphAge_monotone d ell upper
      hCover.upper_age V T hVT).trans hTLe
  have hLocal :=
    integerGraphAgeCanonical_single_bound_locality d ell hell
      upper hCover.upper_age U T (lower U) hOverlap
  have hCanonical :=
    trackFCover_single_support_canonical d ell
      lower upper hCover U hUChanged
  rw [hCanonical] at hLocal
  omega

/-- Every changed support U contains the unique inclusion-minimal
changed support T. This is not true for arbitrary pairs of ordered
functions; genuine graph-age cover uniqueness is essential. -/
theorem trackFCover_essential_contained_in_changed
    (d ell : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (T : IntegerGraphSupport d ell)
    (hTChanged : lower T < upper T)
    (hTMinimal : ∀ V : IntegerGraphSupport d ell,
      V.1 ⊆ T.1 → V.1 ≠ T.1 → lower V = upper V)
    (U : IntegerGraphSupport d ell)
    (hUChanged : lower U < upper U) :
    T.1 ⊆ U.1 := by
  classical
  let candidates : Finset (IntegerGraphSupport d ell) :=
    Finset.univ.filter (fun V =>
      lower V < upper V ∧ V.1 ⊆ U.1)
  have hCandidates : candidates.Nonempty := by
    refine ⟨U, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ U, hUChanged, subset_rfl⟩
  let cards : Finset Nat :=
    candidates.image (fun V => V.1.card)
  have hCards : cards.Nonempty := by
    obtain ⟨V, hV⟩ := hCandidates
    exact ⟨V.1.card, Finset.mem_image.mpr ⟨V,hV,rfl⟩⟩
  obtain ⟨S,hSmem,hScard⟩ :=
    Finset.mem_image.mp (Finset.min'_mem cards hCards)
  have hSChanged : lower S < upper S :=
    (Finset.mem_filter.mp hSmem).2.1
  have hSU : S.1 ⊆ U.1 :=
    (Finset.mem_filter.mp hSmem).2.2
  have hSMinimal : ∀ V : IntegerGraphSupport d ell,
      V.1 ⊆ S.1 → V.1 ≠ S.1 → lower V = upper V := by
    intro V hVS hVNe
    by_contra hDiff
    have hVChanged : lower V < upper V := by
      have hLe := hCover.le V
      omega
    have hVU : V.1 ⊆ U.1 := hVS.trans hSU
    have hVmem : V ∈ candidates :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ V, hVChanged, hVU⟩
    have hVcard : V.1.card ∈ cards :=
      Finset.mem_image.mpr ⟨V,hVmem,rfl⟩
    have hMin : cards.min' hCards ≤ V.1.card :=
      Finset.min'_le cards V.1.card hVcard
    have hStrict : V.1 ⊂ S.1 :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hVS, hVNe⟩
    have hLt : V.1.card < S.1.card :=
      Finset.card_lt_card hStrict
    omega
  have hTS : T = S :=
    integerGraphAgeCover_minimal_changed_unique d ell hell
      lower upper hCover T S
      hTChanged hSChanged hTMinimal hSMinimal
  rw [hTS]
  exact hSU

/-- Part (3) of Lem:Consecutive in the manuscript:
EVERY changed support U has the SAME upper value as the uniquely
minimal changed support T, for genuine K_ell integer-witness ages.

This conclusion actually combines the separately verified cover
one-step theorem, finite minimal-support selection, and true
canonical one-support locality. No abstract assumption is hidden. -/
theorem trackFCover_all_changed_upper_eq_essential
    (d ell : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper) :
    ∃ T : IntegerGraphSupport d ell,
      lower T < upper T ∧
      (∀ V : IntegerGraphSupport d ell,
        V.1 ⊆ T.1 → V.1 ≠ T.1 → lower V = upper V) ∧
      (∀ U : IntegerGraphSupport d ell,
        lower U < upper U → upper U = upper T) := by
  obtain ⟨T,⟨hChanged,hMinimal⟩,_⟩ :=
    trackFCover_unique_minimal_changed d ell hell lower upper hCover
  refine ⟨T,hChanged,hMinimal,?_⟩
  intro U hUChanged
  have hTU : T.1 ⊆ U.1 :=
    trackFCover_essential_contained_in_changed d ell hell
      lower upper hCover T hChanged hMinimal U hUChanged
  have hUStep : upper U = lower U + 1 :=
    trackFCover_drop_one_at_changed d ell
      lower upper hCover U hUChanged
  exact (trackFCover_changed_values_of_containment d ell hell
    lower upper hCover T U
    hChanged hUChanged hTU hUStep).symm

end Kk
