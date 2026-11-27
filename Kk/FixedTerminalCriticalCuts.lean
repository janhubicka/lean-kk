import Kk.FiniteOldColumnAge
import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Bounded critical coordinates on a fixed finite terminal set

The two finite witness families are monotone in the full chronological
prefix. They track first column disagreements and the three relevant
clique-capacity thresholds for every subset of the fixed terminal set.
No graph-freeness premise is needed for the truncated raw-age statement.
This deliberately over-retains; it is not a sharp diary classification.
-/

namespace Kk

noncomputable def fixedCriticalPairs (E : Nat → Nat → Bool)
    (A : Finset Nat) (c : Nat) : Finset (Nat × Nat) := by
  classical
  exact (A.product A).filter (fun ab => ∃ p < c, E p ab.1 ≠ E p ab.2)

noncomputable def fixedCriticalCapacity (E : Nat → Nat → Bool)
    (T : Finset Nat) (c : Nat) : Nat :=
  finiteDirectedCliqueCapacity E
    ((Finset.range c).filter (fun p => ∀ t ∈ T, E p t = true))

noncomputable def fixedCriticalThresholds (E : Nat → Nat → Bool)
    (A : Finset Nat) (c : Nat) : Finset (Finset Nat × Nat) := by
  classical
  exact (A.powerset.product (Finset.range 3)).filter
    (fun tr => tr.2 + 1 ≤ fixedCriticalCapacity E tr.1 c)

theorem fixedCriticalCapacity_mono (E : Nat → Nat → Bool)
    (T : Finset Nat) : Monotone (fixedCriticalCapacity E T) := by
  intro c d hcd
  unfold fixedCriticalCapacity
  apply finiteDirectedCliqueCapacity_mono
  intro p hp
  obtain ⟨hp, hAll⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hp) hcd), hAll⟩

theorem fixedCriticalPairs_mono (E : Nat → Nat → Bool) (A : Finset Nat) :
    Monotone (fixedCriticalPairs E A) := by
  classical
  intro c d hcd ab hab
  obtain ⟨hab, p, hp, hNe⟩ := Finset.mem_filter.mp hab
  exact Finset.mem_filter.mpr ⟨hab, p, lt_of_lt_of_le hp hcd, hNe⟩

theorem fixedCriticalThresholds_mono (E : Nat → Nat → Bool) (A : Finset Nat) :
    Monotone (fixedCriticalThresholds E A) := by
  classical
  intro c d hcd tr htr
  obtain ⟨htr, hThreshold⟩ := Finset.mem_filter.mp htr
  exact Finset.mem_filter.mpr ⟨htr,
    hThreshold.trans (fixedCriticalCapacity_mono E tr.1 hcd)⟩

noncomputable def fixedCriticalRank (E : Nat → Nat → Bool)
    (A : Finset Nat) (c : Nat) : Nat :=
  (fixedCriticalPairs E A c).card + (fixedCriticalThresholds E A c).card

theorem fixedCriticalRank_mono (E : Nat → Nat → Bool) (A : Finset Nat) :
    Monotone (fixedCriticalRank E A) := by
  intro c d hcd
  exact Nat.add_le_add (Finset.card_le_card (fixedCriticalPairs_mono E A hcd))
    (Finset.card_le_card (fixedCriticalThresholds_mono E A hcd))

theorem fixedCriticalRank_le (E : Nat → Nat → Bool) (A : Finset Nat) (c : Nat) :
    fixedCriticalRank E A c ≤ A.card * A.card + 2^A.card * 3 := by
  classical
  have hp : (fixedCriticalPairs E A c).card ≤ A.card * A.card := by
    unfold fixedCriticalPairs
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product _ _)
  have ht : (fixedCriticalThresholds E A c).card ≤ 2^A.card * 3 := by
    unfold fixedCriticalThresholds
    calc
      _ ≤ (A.powerset.product (Finset.range 3)).card := Finset.card_filter_le _ _
      _ = 2^A.card * 3 := by simp [Finset.card_product, Finset.card_powerset]
  exact Nat.add_le_add hp ht

/-- A finite rank budget bounds the number of strictly increasing steps,
regardless of the length of the ambient chronological prefix. -/
theorem strictRankSteps_card_le (r : Nat → Nat) (hr : Monotone r) (b : Nat) :
    ((Finset.range b).filter (fun c => r c < r (c+1))).card ≤ r b := by
  induction b with
  | zero => simp
  | succ b ih =>
      let P := (Finset.range b).filter (fun c => r c < r (c+1))
      have hb : b ∉ P := by simp [P]
      by_cases h : r b < r (b+1)
      · have hSet : (Finset.range (b+1)).filter (fun c => r c < r (c+1)) =
            insert b P := by
          ext c
          simp only [P, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
          constructor
          · rintro ⟨hc, hInc⟩
            by_cases hEq : c = b
            · exact Or.inl hEq
            · exact Or.inr ⟨by omega, hInc⟩
          · rintro (rfl | ⟨hc,hInc⟩)
            · exact ⟨by omega, h⟩
            · exact ⟨by omega, hInc⟩
        rw [hSet, Finset.card_insert_of_notMem hb]
        change P.card ≤ r b at ih
        omega
      · have hSet : (Finset.range (b+1)).filter (fun c => r c < r (c+1)) =
            P := by
          ext c
          simp only [P, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hc, hInc⟩
            have hNe : c ≠ b := by
              intro hEq
              subst c
              exact h hInc
            exact ⟨by omega, hInc⟩
          · rintro ⟨hc, hInc⟩
            exact ⟨by omega, hInc⟩
        rw [hSet]
        exact ih.trans (hr (Nat.le_succ b))

noncomputable def fixedCriticalCuts (E : Nat → Nat → Bool)
    (A : Finset Nat) (b : Nat) : Finset Nat :=
  (Finset.range b).filter (fun c => fixedCriticalRank E A c < fixedCriticalRank E A (c+1))

theorem fixedCriticalCuts_card_le (E : Nat → Nat → Bool) (A : Finset Nat) (b : Nat) :
    (fixedCriticalCuts E A b).card ≤ A.card * A.card + 2^A.card * 3 :=
  (strictRankSteps_card_le _ (fixedCriticalRank_mono E A) b).trans
    (fixedCriticalRank_le E A b)

theorem fixedCriticalRank_eq_of_not_mem (E : Nat → Nat → Bool)
    (A : Finset Nat) (b c : Nat) (hc : c < b)
    (h : c ∉ fixedCriticalCuts E A b) :
    fixedCriticalRank E A c = fixedCriticalRank E A (c+1) := by
  apply Nat.le_antisymm (fixedCriticalRank_mono E A (Nat.le_succ c))
  by_contra hNot
  apply h
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, Nat.lt_of_not_ge hNot⟩

/-- Neither finite witness family can gain an element at a neutral step. -/
theorem fixedCriticalWitnesses_eq (E : Nat → Nat → Bool)
    (A : Finset Nat) (c : Nat)
    (h : fixedCriticalRank E A c = fixedCriticalRank E A (c+1)) :
    fixedCriticalPairs E A c = fixedCriticalPairs E A (c+1) ∧
      fixedCriticalThresholds E A c = fixedCriticalThresholds E A (c+1) := by
  have hp := fixedCriticalPairs_mono E A (Nat.le_succ c)
  have ht := fixedCriticalThresholds_mono E A (Nat.le_succ c)
  have hpc := Finset.card_le_card hp
  have htc := Finset.card_le_card ht
  unfold fixedCriticalRank at h
  exact ⟨Finset.eq_of_subset_of_card_le hp (by omega),
    Finset.eq_of_subset_of_card_le ht (by omega)⟩

/-- A neutral step cannot introduce the first disagreement of any two
members of the fixed set, hence of any selected subfront. -/
theorem fixedCritical_no_split (E : Nat → Nat → Bool) (A : Finset Nat)
    (c u v : Nat) (hu : u ∈ A) (hv : v ∈ A)
    (h : fixedCriticalRank E A c = fixedCriticalRank E A (c+1))
    (hOld : ∀ p < c, E p u = E p v) :
    E c u = E c v := by
  classical
  by_contra hNe
  have hNew : (u,v) ∈ fixedCriticalPairs E A (c+1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hv⟩,
      c, Nat.lt_succ_self c, hNe⟩
  rw [← (fixedCriticalWitnesses_eq E A c h).1] at hNew
  obtain ⟨_,p,hp,hDifferent⟩ := Finset.mem_filter.mp hNew
  exact hDifferent (hOld p hp)

/-- Three thresholds determine the truncated K4 raw bound, even for
arbitrary directed graphs or terminal sets overlapping the prefix. -/
theorem fixedCritical_truncated_eq (E : Nat → Nat → Bool)
    (A T : Finset Nat) (c : Nat) (hT : T ⊆ A)
    (h : fixedCriticalRank E A c = fixedCriticalRank E A (c+1)) :
    3 - fixedCriticalCapacity E T c = 3 - fixedCriticalCapacity E T (c+1) := by
  classical
  have hLe := fixedCriticalCapacity_mono E T (Nat.le_succ c)
  by_contra hNe
  let k := fixedCriticalCapacity E T c
  have hk : k < 3 := by dsimp [k]; omega
  have hInc : k + 1 ≤ fixedCriticalCapacity E T (c+1) := by dsimp [k]; omega
  have hNew : (T,k) ∈ fixedCriticalThresholds E A (c+1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hT, Finset.mem_range.mpr hk⟩, hInc⟩
  rw [← (fixedCriticalWitnesses_eq E A c h).2] at hNew
  have hOld := (Finset.mem_filter.mp hNew).2
  change k + 1 ≤ fixedCriticalCapacity E T c at hOld
  dsimp [k] at hOld
  omega

/-- Raw bounds restrict literally to an arbitrary finite list of
addresses by taking the image of each supported set of sort labels. -/
theorem fixedCritical_raw_image {d : Nat} (E : Nat → Nat → Bool)
    (target : Fin d → Nat) (c : Nat) (T : IntegerGraphSupport d 4) :
    finiteOldColumnRawBound E 4 d (Finset.range c) (fun p i => E p (target i)) T =
      3 - fixedCriticalCapacity E (T.1.image target) c := by
  classical
  have hPool : oldSupportCommonNeighbourPool (Finset.range c)
      (fun p i => E p (target i)) T.1 =
        (Finset.range c).filter (fun p => ∀ t ∈ T.1.image target, E p t = true) := by
    ext p
    simp only [oldSupportCommonNeighbourPool, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hp,hAll⟩
      refine ⟨hp, ?_⟩
      intro t ht
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      exact hAll i hi
    · rintro ⟨hp,hAll⟩
      exact ⟨hp, fun i hi => hAll (target i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)⟩
  unfold finiteOldColumnRawBound fixedCriticalCapacity
  rw [hPool]

theorem fixedCritical_raw_neutral {d : Nat} (E : Nat → Nat → Bool)
    (A : Finset Nat) (target : Fin d → Nat) (hTarget : ∀ i, target i ∈ A)
    (c : Nat) (h : fixedCriticalRank E A c = fixedCriticalRank E A (c+1)) :
    finiteOldColumnRawBound E 4 d (Finset.range c) (fun p i => E p (target i)) =
      finiteOldColumnRawBound E 4 d (Finset.range (c+1)) (fun p i => E p (target i)) := by
  classical
  funext T
  rw [fixedCritical_raw_image, fixedCritical_raw_image]
  apply fixedCritical_truncated_eq E A _ c _ h
  intro t ht
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
  exact hTarget i

end Kk
