import Kk.RetainedPrefixSource
import Mathlib.Tactic

/-!
# Actual level maps enumerate the retained ordinary slots

English proof and independent review were committed before implementation:
`docs/retained_level_enumeration_english_20261124.md` and
`docs/audits/2026-11-24-retained-level-enumeration-review-generation-zero.md`.

An actual strict level map with a represented cap endpoint and the exact
retained range determines its source length and every ordinary coordinate.
The endpoint is counted once and then excluded from the ordinary slots.
The actual Kpt version recovers the complete ordinary source code along
those literal slots, without assuming its size or an inverse-map identity.

The empty ordinary list and zero cap endpoint are allowed. No positive-size
G+ vertex is claimed by these generic enumeration/recovery statements.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Equal literal ranges of two increasing finite enumerations determine
their domain lengths, including either empty-domain boundary. -/
theorem strictMono_fin_size_eq_of_range_eq
    {n m : Nat} (f : Fin n → Nat) (g : Fin m → Nat)
    (hf : StrictMono f) (hg : StrictMono g)
    (hRange : Set.range f = Set.range g) : n = m := by
  have hCard := congrArg Set.ncard hRange
  rw [Set.ncard_range_of_injective hf.injective,
    Set.ncard_range_of_injective hg.injective] at hCard
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hCard

private def retainedSlotsWithEndpoint
    {M : Nat} (slots : Fin M → Nat) (top : Nat)
    (i : Fin (M+1)) : Nat :=
  if hi : i.val < M then slots ⟨i.val,hi⟩ else top

private theorem retainedSlotsWithEndpoint_strictMono
    {M : Nat} (slots : Fin M → Nat) (top : Nat)
    (hSlots : StrictMono slots) (hBelow : ∀ i, slots i < top) :
    StrictMono (retainedSlotsWithEndpoint slots top) := by
  intro i j hij
  by_cases hj : j.val < M
  · have hi : i.val < M := by omega
    simp only [retainedSlotsWithEndpoint, dite_eq_left hi, dite_eq_left hj]
    exact hSlots hij
  · have hi : i.val < M := by
      have hjBound := j.isLt
      omega
    simp only [retainedSlotsWithEndpoint, dite_eq_left hi, dite_eq_right hj]
    exact hBelow _

private theorem retainedSlotsWithEndpoint_range
    {M : Nat} (slots : Fin M → Nat) (top : Nat) :
    Set.range (retainedSlotsWithEndpoint slots top) =
      {q | q ∈ Set.range slots ∨ q = top} := by
  ext q
  constructor
  · rintro ⟨i,hi⟩
    by_cases hSmall : i.val < M
    · exact Or.inl ⟨⟨i.val,hSmall⟩, by
        simpa only [retainedSlotsWithEndpoint, dite_eq_left hSmall] using hi⟩
    · right
      exact (by simpa only [retainedSlotsWithEndpoint,
        dite_eq_right hSmall] using hi : top = q).symm
  · rintro (⟨i,hi⟩ | hq)
    · refine ⟨i.castSucc, ?_⟩
      simpa only [retainedSlotsWithEndpoint, Fin.val_castSucc,
        dite_eq_left i.isLt] using hi
    · subst q
      refine ⟨Fin.last M, ?_⟩
      simp only [retainedSlotsWithEndpoint, Fin.val_last,
        lt_self_iff_false, dite_false]

private theorem strictMono_initial_level_range
    (level : Nat → Nat) (hLevel : StrictMono level) (n : Nat) :
    Set.range (fun i : Fin (n+1) => level i.val) =
      {q | q ∈ Set.range level ∧ q ≤ level n} := by
  ext q
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨⟨i.val,hi⟩, ?_⟩
    rw [← hi]
    exact hLevel.monotone (by have h := i.isLt; omega)
  · rintro ⟨⟨j,hj⟩,hBelow⟩
    have hBound : j ≤ n := by
      by_contra hn
      have hLt : n < j := by omega
      have h := hLevel hLt
      rw [hj] at h
      omega
    exact ⟨⟨j,by omega⟩,hj⟩

/-- Exact range through one actual represented endpoint determines both
source length and every ordinary retained level-map coordinate. The cap
endpoint itself is excluded from the M ordinary coordinates. -/
theorem strictMono_levelMap_eq_slots_of_exact_range
    (level : Nat → Nat) (hLevel : StrictMono level)
    (n top M : Nat) (hEnd : level n = top)
    (slots : Fin M → Nat) (hSlots : StrictMono slots)
    (hBelow : ∀ i, slots i < top)
    (hThrough : ∀ q, q ≤ top →
      (q ∈ Set.range level ↔ q ∈ Set.range slots ∨ q = top)) :
    n = M ∧ (∀ i : Fin M, level i.val = slots i) ∧ level M = top := by
  let first : Fin (n+1) → Nat := fun i => level i.val
  let listed : Fin (M+1) → Nat := retainedSlotsWithEndpoint slots top
  have hFirst : StrictMono first := by
    intro i j hij
    exact hLevel hij
  have hListed : StrictMono listed :=
    retainedSlotsWithEndpoint_strictMono slots top hSlots hBelow
  have hRange : Set.range first = Set.range listed := by
    rw [show first = (fun i : Fin (n+1) => level i.val) from rfl,
      strictMono_initial_level_range level hLevel n, hEnd,
      show listed = retainedSlotsWithEndpoint slots top from rfl,
      retainedSlotsWithEndpoint_range]
    ext q
    constructor
    · rintro ⟨hIn,hBound⟩
      exact (hThrough q hBound).1 hIn
    · intro hIn
      have hBound : q ≤ top := by
        rcases hIn with ⟨i,hi⟩ | hq
        · rw [← hi]
          exact Nat.le_of_lt (hBelow i)
        · rw [hq]
      exact ⟨(hThrough q hBound).2 hIn,hBound⟩
  have hSize : n = M := by
    have hSucc := strictMono_fin_size_eq_of_range_eq
      first listed hFirst hListed hRange
    omega
  subst n
  have hSame : first = listed :=
    (hFirst.range_inj_of_wellFoundedLT hListed).1 hRange
  refine ⟨rfl, ?_, hEnd⟩
  intro i
  have hPoint := congrFun hSame i.castSucc
  simpa only [first, listed, retainedSlotsWithEndpoint,
    Fin.val_castSucc, dite_eq_left i.isLt] using hPoint

/-- For a genuine Kpt shape map with an actual cap preimage, the exact
output level range identifies the source cap level and literal retained
coordinates. No source-size or retained-map equality is an input. -/
theorem kpt_source_level_and_coordinates_of_exact_slot_range
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (F : ShapeMap (admissibleKptSTree family))
    (source target : AdmissibleKptNode family) (hImage : F source = target)
    (M : Nat) (slots : Fin M → Nat) (hSlots : StrictMono slots)
    (hBelow : ∀ i, slots i < LevelTree.lev target)
    (hRange : F.levelRange =
      {q | q ∈ Set.range slots ∨ q = LevelTree.lev target ∨ LevelTree.lev target < q}) :
    LevelTree.lev source = M ∧
      (∀ i : Fin M, kptShapeLevelMap family F i.val = slots i) := by
  have hEnd : kptShapeLevelMap family F (LevelTree.lev source) =
      LevelTree.lev target := by
    rw [kptShapeLevelMap_eq family F source, hImage]
  have hThrough : ∀ q, q ≤ LevelTree.lev target →
      (q ∈ Set.range (kptShapeLevelMap family F) ↔
        q ∈ Set.range slots ∨ q = LevelTree.lev target) := by
    intro q hBound
    rw [kptShapeLevelMap_range family F, hRange]
    change (q ∈ Set.range slots ∨ q = LevelTree.lev target ∨
      LevelTree.lev target < q) ↔
      (q ∈ Set.range slots ∨ q = LevelTree.lev target)
    have hNot : ¬ LevelTree.lev target < q := by omega
    simp only [hNot, or_false]
  have h := strictMono_levelMap_eq_slots_of_exact_range
    (kptShapeLevelMap family F) (kptShapeLevelMap_strictMono family F)
    (LevelTree.lev source) (LevelTree.lev target) M hEnd
    slots hSlots hBelow hThrough
  exact ⟨h.1,h.2.1⟩

/-- Recover the complete ordinary source cap code along the explicitly
listed slots. Its source length and all actual level-map coordinates are
derived from the exact range and cap image, rather than assumed.

This includes all four finite tables and makes no positive-size G+ claim
for an empty slot list or zero cap. -/
theorem kpt_source_ordinaryCode_eq_slots_of_exact_range
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (F : ShapeMap (admissibleKptSTree family))
    (source target : AdmissibleKptNode family) (hImage : F source = target)
    (M : Nat) (slots : Fin M → Nat) (hSlots : StrictMono slots)
    (hBelow : ∀ i, slots i < LevelTree.lev target)
    (hRange : F.levelRange =
      {q | q ∈ Set.range slots ∨ q = LevelTree.lev target ∨ LevelTree.lev target < q}) :
    LevelTree.lev source = M ∧
      RawPartialTypeNode.ordinaryCode source.1 =
        (RawPartialTypeNode.ordinaryCode target.1).reindex M
          (fun i => ⟨slots i,hBelow i⟩) := by
  obtain ⟨hSize,hCoordinates⟩ :=
    kpt_source_level_and_coordinates_of_exact_slot_range
      family F source target hImage M slots hSlots hBelow hRange
  refine ⟨hSize, ?_⟩
  subst target
  have hSize' : source.1.1 = M := hSize
  have hIndices :
      (fun i : Fin M => retainedSocleIndex family F source
        (Fin.cast hSize'.symm i)) =
      (fun i : Fin M => (⟨slots i,hBelow i⟩ : Fin (F source).1.1)) := by
    funext i
    apply Fin.ext
    change kptShapeLevelMap family F i.val = slots i
    exact hCoordinates i
  calc
    RawPartialTypeNode.ordinaryCode source.1 =
        (RawPartialTypeNode.ordinaryCode (F source).1).reindex source.1.1
          (retainedSocleIndex family F source) :=
      (shapeMap_recovers_ordinaryCode F source).symm
    _ = (RawPartialTypeNode.ordinaryCode (F source).1).reindex M
        (fun i => retainedSocleIndex family F source (Fin.cast hSize'.symm i)) :=
      (FinitePartialCode.reindex_change_size
        (RawPartialTypeNode.ordinaryCode (F source).1) hSize'
        (retainedSocleIndex family F source)).symm
    _ = (RawPartialTypeNode.ordinaryCode (F source).1).reindex M
        (fun i => ⟨slots i,hBelow i⟩) :=
      congrArg (fun rho : Fin M → Fin (F source).1.1 =>
        (RawPartialTypeNode.ordinaryCode (F source).1).reindex M rho) hIndices

#print axioms Kk.strictMono_fin_size_eq_of_range_eq
#print axioms Kk.strictMono_levelMap_eq_slots_of_exact_range
#print axioms Kk.kpt_source_level_and_coordinates_of_exact_slot_range
#print axioms Kk.kpt_source_ordinaryCode_eq_slots_of_exact_range

end Kk
