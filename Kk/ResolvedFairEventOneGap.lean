import Kk.ResolvedFairEventSchedule
import Kk.ResolvedFairOneGap

/-!
# Canonical one-gap sources for the actual individual-event chronology

English proof, reviewed before implementation:
`docs/resolved_fair_event_one_gap_english_20261127.md`.
The actual initial stage has empty old pool by definition. No diary
parser, common inverse-source orbit, or Ramsey bound is asserted here.
-/

namespace Kk
open SuccessorTree.V10

noncomputable def resolvedFairEventOneGapPartial
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    CountableEnumeratedPartialStructure 1 0 1 :=
  oneGapPartial (resolvedFairEventEdge s0)

theorem resolvedFairEventOneGapPartial_avoids
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (by omega) →
      bad.Avoids (resolvedFairEventOneGapPartial s0).L :=
  oneGapPartial_avoids (resolvedFairEventEdge s0) 4 (by omega)
    (henson_avoids_of_finite_clique_bound (resolvedFairEventEdge s0)
      4 (by omega) (resolvedFairEventEdge_free s0 hEmpty)
      (resolvedFairEventEdge_sym s0) (resolvedFairEventEdge_loops s0))

/-- The actual canonical source at each original's individual-event position. -/
noncomputable def resolvedFairEventOneGapOriginal
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) (i : Nat) :
    FiniteGPlusVertex (hensonForbiddenFamily 4 (by omega)) :=
  (resolvedFairEventOneGapPartial s0).toGPlus (hensonForbiddenFamily 4 (by omega))
    (resolvedFairEventOneGapPartial_avoids s0 hEmpty)
    (oneGapAddress (resolvedFairEventCodePosition s0 i))

theorem resolvedFairEventOneGapOriginal_size
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) (i : Nat) :
    (resolvedFairEventOneGapOriginal s0 hEmpty i).val.size =
      2 * resolvedFairEventCodePosition s0 i + 3 := by
  change oneGapAddress (resolvedFairEventCodePosition s0 i) + 1 = _
  unfold oneGapAddress
  omega

theorem resolvedFairEventOneGapOriginal_strictMono_size
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) :
    StrictMono (fun i => (resolvedFairEventOneGapOriginal s0 hEmpty i).val.size) := by
  intro i j hij
  have hi := resolvedFairEventOneGapOriginal_size s0 hEmpty i
  have hj := resolvedFairEventOneGapOriginal_size s0 hEmpty j
  have h := resolvedFairEventCodePosition_strictMono s0 hij
  dsimp only
  omega

theorem resolvedFairEventOneGapOriginal_injective
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) :
    Function.Injective (resolvedFairEventOneGapOriginal s0 hEmpty) := by
  intro i j hij
  exact (resolvedFairEventOneGapOriginal_strictMono_size s0 hEmpty).injective
    (congrArg (fun v : FiniteGPlusVertex (hensonForbiddenFamily 4 (by omega)) =>
      v.val.size) hij)

/-- Exact ordinary bits, including nonedges, in either direction. -/
theorem resolvedFairEventOneGapOriginal_binary
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (i j : Nat) (hij : i ≠ j) :
    finiteGPlusBinary (resolvedFairEventOneGapOriginal s0 hEmpty i)
      (resolvedFairEventOneGapOriginal s0 hEmpty j) 0 = s0.edge (2*i) (2*j) := by
  have hAddress : oneGapAddress (resolvedFairEventCodePosition s0 i) ≠
      oneGapAddress (resolvedFairEventCodePosition s0 j) := by
    intro h
    exact hij ((resolvedFairEventCodePosition_strictMono s0).injective
      (oneGapAddress_strictMono.injective h))
  unfold resolvedFairEventOneGapOriginal
  rw [CountableEnumeratedPartialStructure.toGPlus_binary _ _ _ hAddress]
  change oneGapEdge (resolvedFairEventEdge s0)
    (oneGapAddress (resolvedFairEventCodePosition s0 i))
    (oneGapAddress (resolvedFairEventCodePosition s0 j)) = _
  rw [oneGapEdge_address]
  exact resolvedFairEventEdge_originals s0 i j

theorem resolvedFairEventOneGapOriginal_diagonal
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) (i : Nat) :
    finiteGPlusDiagonal (resolvedFairEventOneGapOriginal s0 hEmpty i) 0 = false := by
  unfold resolvedFairEventOneGapOriginal
  rw [CountableEnumeratedPartialStructure.toGPlus_diagonal]
  change oneGapEdge (resolvedFairEventEdge s0)
    (oneGapAddress (resolvedFairEventCodePosition s0 i))
    (oneGapAddress (resolvedFairEventCodePosition s0 i)) = false
  rw [oneGapEdge_address]
  exact resolvedFairEventEdge_loops s0 _

/-- All auxiliary atoms on originals are exactly their strict chronological order. -/
theorem resolvedFairEventOneGapOriginal_E
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) (i j : Nat) :
    finiteGPlusE (resolvedFairEventOneGapOriginal s0 hEmpty i)
      (resolvedFairEventOneGapOriginal s0 hEmpty j) = decide (i < j) := by
  unfold resolvedFairEventOneGapOriginal
  rw [CountableEnumeratedPartialStructure.toGPlus_E]
  change oneGapAux (oneGapAddress (resolvedFairEventCodePosition s0 i))
    (oneGapAddress (resolvedFairEventCodePosition s0 j)) = _
  simp only [oneGapAux, oneGapAddress_real, true_and]
  have hSpace : oneGapAddress (resolvedFairEventCodePosition s0 i) + 1 <
      oneGapAddress (resolvedFairEventCodePosition s0 j) ↔ i < j := by
    have hMono : resolvedFairEventCodePosition s0 i < resolvedFairEventCodePosition s0 j ↔
        i < j := (resolvedFairEventCodePosition_strictMono s0).lt_iff_lt
    unfold oneGapAddress
    omega
  simp only [hSpace]

/-- The application has no extra initial-pool premise: its empty pool is definitional. -/
theorem resolvedInitialEventOneGapOriginal_binary
    (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false)
    (i j : Nat) (hij : i ≠ j) :
    let s0 := resolvedInitialStage E hFree hSym hLoops
    finiteGPlusBinary (resolvedFairEventOneGapOriginal s0 (by rfl) i)
      (resolvedFairEventOneGapOriginal s0 (by rfl) j) 0 = E i j := by
  dsimp only
  have hEmpty : (resolvedInitialStage E hFree hSym hLoops).old = ∅ := rfl
  refine (resolvedFairEventOneGapOriginal_binary
    (resolvedInitialStage E hFree hSym hLoops) hEmpty i j hij).trans ?_
  change E (2*i/2) (2*j/2) = E i j
  congr 1 <;> omega

end Kk
