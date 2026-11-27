import Kk.ResolvedFairRetainedPalette
import Kk.ResolvedFairEventOneGap
import SuccessorTree.V10.GPlusCommonUpperRepresentation
import SuccessorTree.V10.GPlusOrdinaryCode
import Mathlib.Tactic

/-!
# Actual finite palette coverage for all selected K4-free tuples

The upper endpoint is the full original type of the fresh coding cap,
not a new artificial neutral cap. Its free level is one below the
padded cap address. Every selected original is at least two padded
coordinates earlier. Its literal complete prefix is represented by the
ancestor at its own retained address and this common upper endpoint.

This uses the actual bounded-envelope construction and the pinned
successor-tree palette theorem. No sharp diary classification is assumed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

/-- The complete ordinary code of a full original type from a finite
prefix is exactly the corresponding prefix of the countable structure.
The distinguished type vertex is forgotten, but no ordinary atom is. -/
theorem countableOriginal_ordinaryCode
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (N : Nat) (v : Fin N)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids (C.finitePrefix N).L) :
    let U := (C.finitePrefix N).kptOriginal family hAvoid v
    RawPartialTypeNode.ordinaryCode U.1 = C.prefixCode (LevelTree.lev U) := by
  dsimp only
  let B := C.finitePrefix N
  let l := B.freeLevel v.val
  have hl : l ≤ N := (B.freeLevel_le v.val).trans (Nat.le_of_lt v.isLt)
  change RawPartialTypeNode.ordinaryCode
    (⟨l, B.partialTypeAt l v.val⟩ : RawPartialTypeNode db du dd) =
      C.prefixCode l
  have hRestrict : ∀ (D E : FinitePartialCode db du dd) (h : D = E)
      (d : Nat) (hD : d ≤ D.size) (hE : d ≤ E.size),
      D.restrict d hD = E.restrict d hE := by
    intro D E h d hD hE
    subst E
    rfl
  calc
    _ = FinitePartialCode.ofEnumerated (B.initialSegment l hl) :=
      (B.initialSegment_code_eq_ordinaryCode l v.val hl).symm
    _ = (FinitePartialCode.ofEnumerated B).restrict l hl :=
      (FinitePartialCode.ofEnumerated_initialSegment B l hl).symm
    _ = (C.prefixCode N).restrict l hl :=
      hRestrict _ _ (C.ofEnumerated_finitePrefix N) l hl hl
    _ = C.prefixCode l := C.prefixCode_restrict l N hl

/-- Construct the literal G+ pair for each requested original using
the actual common upper cap, even with arbitrary auxiliary keep flags.
Its lower endpoint need not itself belong to the initial full seed
set: it is a retained ancestor of the covered cap. -/
theorem resolvedFairSelection_actualPair
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool) (i : Nat) (hi : i ∈ S) :
    ∃ P : GPlusRepresentingPair (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3))),
      P.vertex = resolvedFairEventOneGapOriginal s0 hEmpty i ∧
      P.upper ∈ resolvedFairFiniteOriginalSeeds s0 hEmpty S ∧
      LevelTree.lev P.upper ≤ resolvedFairRetainedTop s0 (resolvedFairSelectionCap S) ∧
      LevelTree.lev P.lower ∈ resolvedFairRetainedLevels s0
        (resolvedFairFiniteKeep s0 S auxKeep) (resolvedFairSelectionCap S) := by
  classical
  let n := resolvedFairSelectionCap S
  let N := resolvedFairRetainedSize s0 n
  let C := resolvedFairEventOneGapPartial s0
  have hn : n ∈ resolvedFairSelectionWithCap S := Finset.mem_insert_self _ _
  let v := resolvedFairFiniteSelectionVertex s0 S n hn
  let U := resolvedFairOriginalType s0 hEmpty n v
  let A := resolvedFairEventOneGapOriginal s0 hEmpty i
  have hv : v.val = resolvedFairOriginalAddress s0 n := rfl
  have hFree : LevelTree.lev U = resolvedFairOriginalAddress s0 n - 1 := by
    change ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N).freeLevel v.val = _
    rw [oneGapPartial_freeLevel _ _ _ v.isLt, hv]
    have hReal : oneGapReal (resolvedFairOriginalAddress s0 n) := oneGapAddress_real _
    exact if_pos hReal
  have hOrd : RawPartialTypeNode.ordinaryCode U.1 =
      C.prefixCode (LevelTree.lev U) :=
    countableOriginal_ordinaryCode (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3))) C N v
      (oneGap_finitePrefix_avoids (resolvedFairEventEdge s0) 4 (by omega)
        (resolvedFairEventGraph_avoids s0 hEmpty) N)
  have hBefore : resolvedFairEventCodePosition s0 i <
      resolvedFairEventCodePosition s0 n :=
    resolvedFairEventCodePosition_strictMono s0
      (resolvedFairSelection_lt_cap S i hi)
  have hLen : A.val.size ≤ LevelTree.lev U := by
    rw [hFree]
    change oneGapAddress (resolvedFairEventCodePosition s0 i) + 1 ≤
      oneGapAddress (resolvedFairEventCodePosition s0 n) - 1
    unfold oneGapAddress
    omega
  have hPrefix : A.val.IsPrefix (RawPartialTypeNode.ordinaryCode U.1) := by
    rw [hOrd]
    refine ⟨hLen, ?_⟩
    change C.prefixCode (A.val.size) =
      (C.prefixCode (LevelTree.lev U)).restrict A.val.size hLen
    exact (C.prefixCode_restrict A.val.size (LevelTree.lev U) hLen).symm
  let P := GPlusRepresentingPair.fromUpper U A.val.size
    (finiteGPlusVertex_size_pos A) hPrefix.1
  have hP : P.vertex = A :=
    GPlusRepresentingPair.fromUpper_vertex_eq_of_prefix U A hPrefix
  have hUpper : P.upper ∈ resolvedFairFiniteOriginalSeeds s0 hEmpty S :=
    resolvedFairFiniteSelectionType_mem_seeds s0 hEmpty S n hn
  have hBound : LevelTree.lev P.upper ≤ resolvedFairRetainedTop s0 n := by
    change LevelTree.lev U ≤ _
    rw [hFree]
    change oneGapAddress (resolvedFairEventCodePosition s0 n) - 1 ≤
      oneGapAddress (resolvedFairEventCodePosition s0 n)
    omega
  have hLower : LevelTree.lev P.lower = resolvedFairOriginalAddress s0 i := by
    change A.val.size - 1 = _
    change oneGapAddress (resolvedFairEventCodePosition s0 i) + 1 - 1 =
      oneGapAddress (resolvedFairEventCodePosition s0 i)
    omega
  refine ⟨P, hP, hUpper, hBound, ?_⟩
  rw [hLower]
  exact resolvedFairFiniteSelection_mem_levels s0 S auxKeep i
    (Finset.mem_insert_of_mem hi)

/-- Every injectively labelled q-tuple of the actual constructed copy,
without a bound on the original indices. -/
def resolvedFairActualTuples
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (q : Nat) :
    Set (Fin q → FiniteGPlusVertex (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)))) :=
  Set.range (fun f : Fin q ↪ Nat => fun i =>
    resolvedFairEventOneGapOriginal s0 hEmpty (f i))

def resolvedFairPaletteBudget (q : Nat) : Nat :=
  6 * resolvedFairRetentionBudget (q + 1) + 1

/-- Actual uniform palette coverage for every finite tuple of originals,
using the cap of its finite index set and ONE genuine envelope map. -/
theorem resolvedFairActualTuples_paletteCover
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (q : Nat) :
    FiniteGPlusPaletteCovers (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)))
      (resolvedFairPaletteBudget q) q (resolvedFairActualTuples s0 hEmpty q) := by
  classical
  intro t ht
  obtain ⟨f, rfl⟩ := ht
  let S := (Finset.univ : Finset (Fin q)).image f
  have hS : S.card = q := by
    change ((Finset.univ : Finset (Fin q)).image f).card = q
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  let n := resolvedFairSelectionCap S
  let keep := resolvedFairCriticalKeep s0 S
  let I := resolvedFairRetainedLevels s0 keep n
  obtain ⟨hCard, F, hInv, hRange⟩ :=
    resolvedFairCriticalFiniteSelection_envelope s0 hEmpty S
  have hBudget : I.card ≤ resolvedFairPaletteBudget q := by
    change I.card ≤ 6 * resolvedFairRetentionBudget (S.card + 1) + 1 at hCard
    rw [hS] at hCard
    exact hCard
  have hPairs : ∀ i : Fin q, ∃ P : GPlusRepresentingPair
      (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3))),
      P.vertex = resolvedFairEventOneGapOriginal s0 hEmpty (f i) ∧
      P.upper ∈ resolvedFairFiniteOriginalSeeds s0 hEmpty S ∧
      LevelTree.lev P.upper ≤ resolvedFairRetainedTop s0 n ∧
      LevelTree.lev P.lower ∈ I := by
    intro i
    exact resolvedFairSelection_actualPair s0 hEmpty S
      (resolvedFairCriticalAuxKeep s0 S) (f i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  choose P hP using hPairs
  have hUpper : ∀ i, (P i).upper ∈ Set.range F.map := by
    intro i
    exact hInv.1.1 (subset_closure
      (admissibleKptSTree (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3))))
      (I : Set Nat) (resolvedFairFiniteOriginalSeeds s0 hEmpty S) (hP i).2.1)
  obtain ⟨e, a, hFact⟩ := retained_pairs_finiteApprox_cover F I
    (resolvedFairRetainedTop s0 n) (resolvedFairPaletteBudget q) q
    hRange hBudget P hUpper
    (fun i => (hP i).2.2.1) (fun i => (hP i).2.2.2)
  refine ⟨e, a, ?_⟩
  intro i
  exact (hFact i).trans (hP i).1

/-- A single genuine successor-tree Ramsey map bounds colours on ALL
q-tuples of the constructed original copy, by a finite palette depending
only on q. This is a coarse upper transfer, not the sharp BRD count. -/
theorem resolvedFairActualTuples_colour_bound
    {κ : Type*} [Fintype κ]
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (q : Nat)
    (χ : (Fin q → FiniteGPlusVertex (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)))) → κ) :
    ∃ (W : SMTree.ShapeSubspace
          (normalizedKptSMTree (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)))) 0)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)))
          (resolvedFairPaletteBudget q) q) ∧
      ∀ t, t ∈ resolvedFairActualTuples s0 hEmpty q →
        χ (fun i : Fin q => gPlusShapeImage W.1.map (t i)) ∈ colours := by
  exact normalizedKpt_GPlus_finite_colour_bound_of_cover
    (hensonForbiddenFamily 4 (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3))) (resolvedFairPaletteBudget q) q
    (resolvedFairActualTuples s0 hEmpty q) χ
    (resolvedFairActualTuples_paletteCover s0 hEmpty q)

end Kk
