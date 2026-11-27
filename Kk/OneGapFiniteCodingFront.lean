import Kk.OneGapFullClosure
import Mathlib.Data.Finset.Sort

/-!
# Constructed finite selected coding fronts

English proof and pre-code review:
`docs/finite_selected_front_english_20261127.md`.
The list contains exactly the eligible kept coding names in the actual
finite pool. Neither positive-source coverage nor old-zero is assumed.
-/

namespace Kk
open SuccessorTree.V10

noncomputable def oneGapCodingFrontSet
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat) : Finset (Fin A.size) := by
  classical
  exact Finset.univ.filter (fun v => v ∈ V ∧ cut+1 ≤ A.freeLevel v.val ∧
    role v.val = .coded true)

noncomputable def oneGapCodingFrontSize
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat) : Nat :=
  (oneGapCodingFrontSet A role V cut).card

noncomputable def oneGapCodingFrontEntry
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat)
    (i : Fin (oneGapCodingFrontSize A role V cut)) : Fin A.size :=
  (oneGapCodingFrontSet A role V cut).orderEmbOfFin rfl i

noncomputable def oneGapCodingFrontSelected
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat)
    (i : Fin (oneGapCodingFrontSize A role V cut)) : Nat :=
  (oneGapCodingFrontEntry A role V cut i).val

theorem oneGapCodingFrontSet_mem
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat) (v : Fin A.size) :
    v ∈ oneGapCodingFrontSet A role V cut ↔
      v ∈ V ∧ cut+1 ≤ A.freeLevel v.val ∧ role v.val = .coded true := by
  classical
  simp [oneGapCodingFrontSet]

theorem oneGapCodingFrontEntry_mem
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat)
    (i : Fin (oneGapCodingFrontSize A role V cut)) :
    oneGapCodingFrontEntry A role V cut i ∈ oneGapCodingFrontSet A role V cut :=
  (oneGapCodingFrontSet A role V cut).orderEmbOfFin_mem rfl i

theorem oneGapCodingFrontSelected_lt_size
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat)
    (i : Fin (oneGapCodingFrontSize A role V cut)) :
    oneGapCodingFrontSelected A role V cut i < A.size :=
  (oneGapCodingFrontEntry A role V cut i).isLt

theorem oneGapCodingFrontSelected_mem_pool
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat)
    (i : Fin (oneGapCodingFrontSize A role V cut)) :
    oneGapCodingFrontEntry A role V cut i ∈ V :=
  ((oneGapCodingFrontSet_mem A role V cut _).mp
    (oneGapCodingFrontEntry_mem A role V cut i)).1

theorem oneGapCodingFrontSelected_eligible
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat)
    (i : Fin (oneGapCodingFrontSize A role V cut)) :
    cut+1 ≤ A.freeLevel (oneGapCodingFrontSelected A role V cut i) :=
  ((oneGapCodingFrontSet_mem A role V cut _).mp
    (oneGapCodingFrontEntry_mem A role V cut i)).2.1

theorem oneGapCodingFrontSelected_coded
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat)
    (i : Fin (oneGapCodingFrontSize A role V cut)) :
    role (oneGapCodingFrontSelected A role V cut i) = .coded true :=
  ((oneGapCodingFrontSet_mem A role V cut _).mp
    (oneGapCodingFrontEntry_mem A role V cut i)).2.2

theorem oneGapCodingFrontSelected_after_cut
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat)
    (i : Fin (oneGapCodingFrontSize A role V cut)) :
    cut < oneGapCodingFrontSelected A role V cut i := by
  have he := oneGapCodingFrontSelected_eligible A role V cut i
  have hf := A.freeLevel_le (oneGapCodingFrontSelected A role V cut i)
  omega

theorem oneGapCodingFrontSelected_strictMono
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat) :
    StrictMono (oneGapCodingFrontSelected A role V cut) := by
  intro i j hij
  exact ((oneGapCodingFrontSet A role V cut).orderEmbOfFin rfl).strictMono hij

theorem oneGapCodingFrontSelected_injective
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat) :
    Function.Injective (oneGapCodingFrontSelected A role V cut) :=
  (oneGapCodingFrontSelected_strictMono A role V cut).injective

/-- This exact range identity includes an empty front. -/
theorem oneGapCodingFrontSelected_range
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat) (v : Fin A.size) :
    (∃ i, v.val = oneGapCodingFrontSelected A role V cut i) ↔
      v ∈ V ∧ cut+1 ≤ A.freeLevel v.val ∧ role v.val = .coded true := by
  constructor
  · rintro ⟨i, hi⟩
    have hEq : v = oneGapCodingFrontEntry A role V cut i := Fin.ext hi
    rw [hEq]
    exact (oneGapCodingFrontSet_mem A role V cut _).mp
      (oneGapCodingFrontEntry_mem A role V cut i)
  · intro hv
    have hRange : v ∈ Set.range ((oneGapCodingFrontSet A role V cut).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact (oneGapCodingFrontSet_mem A role V cut v).mpr hv
    obtain ⟨i, hi⟩ := hRange
    exact ⟨i, (congrArg Fin.val hi).symm⟩

theorem oneGapCodingFrontSize_le_size
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat) :
    oneGapCodingFrontSize A role V cut ≤ A.size := by
  classical
  have h := Finset.card_le_card
    (show oneGapCodingFrontSet A role V cut ⊆ Finset.univ from Finset.subset_univ _)
  simpa [oneGapCodingFrontSize] using h

theorem oneGapCodingFrontSize_zero_iff
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) (cut : Nat) :
    oneGapCodingFrontSize A role V cut = 0 ↔
      ∀ v ∈ V, cut+1 ≤ A.freeLevel v.val → role v.val ≠ .coded true := by
  constructor
  · intro h v hv he hc
    have hm := (oneGapCodingFrontSet_mem A role V cut v).mpr ⟨hv, he, hc⟩
    have hEmpty : oneGapCodingFrontSet A role V cut = ∅ := Finset.card_eq_zero.mp h
    simp [hEmpty] at hm
  · intro h
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hV, he, hc⟩ := (oneGapCodingFrontSet_mem A role V cut v).mp hv
    exact h v hV he hc

theorem oneGapCodingFrontSet_antitone
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) : Antitone (oneGapCodingFrontSet A role V) := by
  intro c d hcd v hv
  obtain ⟨hV, he, hc⟩ := (oneGapCodingFrontSet_mem A role V d v).mp hv
  exact (oneGapCodingFrontSet_mem A role V c v).mpr ⟨hV, by omega, hc⟩

theorem oneGapCodingFrontSize_antitone
    (A : EnumeratedPartialStructure 1 0 1) (role : Nat → ResolvedQBaseRole)
    (V : Set (Fin A.size)) : Antitone (oneGapCodingFrontSize A role V) := by
  intro c d hcd
  exact Finset.card_le_card (oneGapCodingFrontSet_antitone A role V hcd)

end Kk
