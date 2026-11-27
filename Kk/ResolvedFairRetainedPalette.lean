import Kk.ResolvedFairCriticalRetention
import SuccessorTree.V10.GPlusFiniteBigRamseyTransfer
import SuccessorTree.V10.GPlusAlgorithmFinitePalette
import Mathlib.Tactic

/-!
# Bounded G+ palette from a prescribed retained-level envelope

A covered cap and retained lower endpoint levels suffice: order
preservation and uniqueness of ancestors cover the other endpoints.
No minimal AlgorithmRun hypothesis is required. This is a coarse
palette bridge, not a classification of diary histories.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

theorem retained_preimage_level_lt_card
    (F : SMTree.MMap (normalizedKptSMTree family))
    (I : Finset Nat) (top : Nat)
    (hRange : F.map.levelRange = {q | q ∈ I ∨ top < q})
    (y : AdmissibleKptNode family)
    (hy : LevelTree.lev (F.map y) ≤ top) :
    LevelTree.lev y < I.card := by
  classical
  let H := normalizedKptSMTree family
  have hSub : prefixLevels H F (LevelTree.lev y + 1) ⊆ I := by
    intro q hq
    obtain ⟨j, hj, hjq⟩ := (mem_prefixLevels_iff H F (LevelTree.lev y + 1) q).mp hq
    have hMono := (H.levelMap_strictMono F.map).monotone (Nat.lt_succ_iff.mp hj)
    rw [hjq, H.levelMap_eq F.map (a := y)] at hMono
    have hqRange : q ∈ F.map.levelRange := by
      rw [← H.range_levelMap F.map]
      exact ⟨j, hjq⟩
    rw [hRange] at hqRange
    change q ∈ I ∨ top < q at hqRange
    exact hqRange.resolve_right (by omega)
  have hCard := Finset.card_le_card hSub
  rw [card_prefixLevels] at hCard
  omega

theorem retained_ancestor_mem_range
    (F : SMTree.MMap (normalizedKptSMTree family))
    (a b : AdmissibleKptNode family)
    (hab : a ≤ b) (hb : b ∈ Set.range F.map)
    (ha : LevelTree.lev a ∈ F.map.levelRange) :
    a ∈ Set.range F.map := by
  let H := normalizedKptSMTree family
  obtain ⟨u, hu⟩ := hb
  rw [← H.range_levelMap F.map] at ha
  obtain ⟨j, hj⟩ := ha
  have hU : H.levelMap F.map (LevelTree.lev u) = LevelTree.lev b :=
    (H.levelMap_eq F.map (a := u)).trans (congrArg LevelTree.lev hu)
  have hAB := LevelTree.level_le_of_le hab
  have hJ : j ≤ LevelTree.lev u := by
    by_contra hNot
    have h := H.levelMap_strictMono F.map (Nat.lt_of_not_ge hNot)
    rw [hU, hj] at h
    omega
  let v := LevelTree.ancestor u j hJ
  have hvLe : F.map v ≤ b := by
    rw [← hu]
    exact F.map.map_le_of_le (LevelTree.ancestor_le u j hJ)
  have hvLev : LevelTree.lev (F.map v) = LevelTree.lev a := by
    rw [← H.levelMap_eq F.map (a := v)]
    have hv : LevelTree.lev v = j := LevelTree.level_ancestor u j hJ
    rw [hv, hj]
  exact ⟨v, (LevelTree.eq_ancestor_of_le hvLe hvLev hAB).trans
    (LevelTree.eq_ancestor_of_le hab rfl hAB).symm⟩

theorem retained_pair_bounded_lift
    (F : SMTree.MMap (normalizedKptSMTree family))
    (I : Finset Nat) (top : Nat)
    (hRange : F.map.levelRange = {q | q ∈ I ∨ top < q})
    (P : GPlusRepresentingPair family)
    (hUpper : P.upper ∈ Set.range F.map)
    (hBound : LevelTree.lev P.upper ≤ top)
    (hLower : LevelTree.lev P.lower ∈ I) :
    ∃ Q : BoundedGPlusRepresentingPair family I.card,
      gPlusShapeImage F.map Q.val.vertex = P.vertex := by
  have hlRange : LevelTree.lev P.lower ∈ F.map.levelRange := by
    rw [hRange]
    exact Or.inl hLower
  have hl := retained_ancestor_mem_range F P.lower P.upper
    P.lower_lt_upper.le hUpper hlRange
  have hPrefix : IsPrefixEnvelope F.map I.card
      ({P.lower, P.upper} : Set (AdmissibleKptNode family)) := by
    intro x hx
    rcases (show x = P.lower ∨ x = P.upper from by simpa using hx) with rfl | rfl
    · obtain ⟨y, hy⟩ := hl
      refine ⟨y, retained_preimage_level_lt_card F I top hRange y ?_, hy⟩
      rw [hy]
      exact (LevelTree.level_le_of_le P.lower_lt_upper.le).trans hBound
    · obtain ⟨y, hy⟩ := hUpper
      refine ⟨y, retained_preimage_level_lt_card F I top hRange y ?_, hy⟩
      rwa [hy]
  obtain ⟨Q, hQ⟩ := boundedGPlusPair_lift_of_prefixEnvelope family F.map I.card
    ({P.lower, P.upper} : Set _) hPrefix P (by simp) (by simp)
  exact ⟨Q, (Q.val.image_vertex_eq_canonicalShapeImage F.map).symm.trans hQ⟩

theorem retained_pairs_finiteApprox_cover
    (F : SMTree.MMap (normalizedKptSMTree family))
    (I : Finset Nat) (top b q : Nat)
    (hRange : F.map.levelRange = {l | l ∈ I ∨ top < l})
    (hCard : I.card ≤ b)
    (P : Fin q → GPlusRepresentingPair family)
    (hUpper : ∀ i, (P i).upper ∈ Set.range F.map)
    (hBound : ∀ i, LevelTree.lev (P i).upper ≤ top)
    (hLower : ∀ i, LevelTree.lev (P i).lower ∈ I) :
    ∃ (e : boundedGPlusPaletteIndices family b q)
        (a : SMTree.AM (normalizedKptSMTree family) 0 (b + 1)),
        ∀ i, gPlusShapeImage (a.representative (normalizedKptSMTree family)).map
          (e.val i) = (P i).vertex := by
  classical
  choose Q hQ using fun i => retained_pair_bounded_lift F I top hRange
    (P i) (hUpper i) (hBound i) (hLower i)
  let Q' : Fin q → BoundedGPlusRepresentingPair family b :=
    fun i => ⟨(Q i).val, (Q i).property.trans hCard⟩
  let t : Fin q → FiniteGPlusVertex family := fun i => (Q' i).val.vertex
  have ht : t ∈ boundedGPlusTuplePalette family b q := ⟨Q', rfl⟩
  let H := normalizedKptSMTree family
  have hFix : F.FixesBelow H 0 := by intro x hx; omega
  let a := F.toAM H 0 (b + 1) hFix
  have hAgree : ∀ x : AdmissibleKptNode family,
      LevelTree.lev x ≤ b → (a.representative H).map x = F.map x := by
    intro x hx
    exact SMTree.MMap.toAM_representative_agrees H F 0 (b + 1) hFix x (by omega)
  have hTuple := gPlusShapeImage_eq_of_agree_bounded_tuple family b q
    (a.representative H).map F.map hAgree t ht
  refine ⟨⟨t, ht⟩, a, ?_⟩
  intro i
  exact (congrFun hTuple i).trans (hQ i)

end Kk
