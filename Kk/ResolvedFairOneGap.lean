import Kk.ResolvedFairChronological
import Kk.OneGapPartialStructure

/-!
# The constructed fair graph in the genuine one-gap G+ source

This constructs forbidden avoidance and the canonical source embedding.
No abstract representation or pre-existing resolved graph is assumed.
It does not assert envelope-source equality or a Ramsey bound.

English proof: `docs/resolved_fair_one_gap_english_20261126.md`.
-/

namespace Kk
open SuccessorTree.V10

theorem henson_avoids_of_finite_clique_bound
    (G : Nat → Nat → Bool) (ell : Nat) (hell : 2 ≤ ell)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn G C → C.card < ell)
    (hSym : ∀ x y, G x y = G y x) (hLoops : ∀ x, G x x = false) :
    ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel G) := by
  classical
  apply (hensonForbiddenFamily_avoids_iff ell hell G).mpr
  refine ⟨hLoops,hSym,?_⟩
  rintro ⟨f,hf,hEdges⟩
  have hClique : IsDirectedCliqueOn G ((Finset.univ : Finset (Fin ell)).image f) := by
    intro x hx y hy hxy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    exact hEdges i j (fun h => hxy (congrArg f h))
  have hBound := hFree _ hClique
  have hCard : ((Finset.univ : Finset (Fin ell)).image f).card = ell := by
    simpa using Finset.card_image_of_injective (Finset.univ : Finset (Fin ell))
      hf.injective
  omega

noncomputable def resolvedFairOneGapPartial
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    CountableEnumeratedPartialStructure 1 0 1 :=
  oneGapPartial (resolvedFairChronologicalEdge s0)

theorem resolvedFairOneGapPartial_avoids
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (by omega) →
      bad.Avoids (resolvedFairOneGapPartial s0).L :=
  oneGapPartial_avoids (resolvedFairChronologicalEdge s0) 4 (by omega)
    (henson_avoids_of_finite_clique_bound (resolvedFairChronologicalEdge s0)
      4 (by omega) (resolvedFairChronologicalEdge_free s0)
      (resolvedFairChronologicalEdge_sym s0) (resolvedFairChronologicalEdge_loops s0))

/-- Actual finite-prefix G+ vertex of each prescribed original. -/
noncomputable def resolvedFairOneGapOriginal
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i : Nat) :
    FiniteGPlusVertex (hensonForbiddenFamily 4 (by omega)) :=
  (resolvedFairOneGapPartial s0).toGPlus (hensonForbiddenFamily 4 (by omega))
    (resolvedFairOneGapPartial_avoids s0)
    (oneGapAddress (resolvedFairCodePosition s0 i))

theorem resolvedFairOneGapOriginal_size
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i : Nat) :
    (resolvedFairOneGapOriginal s0 i).val.size =
      2 * resolvedFairCodePosition s0 i + 3 := by
  change oneGapAddress (resolvedFairCodePosition s0 i) + 1 = _
  unfold oneGapAddress
  omega

theorem resolvedFairOneGapOriginal_strictMono_size
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    StrictMono (fun i => (resolvedFairOneGapOriginal s0 i).val.size) := by
  intro i j hij
  have hi := resolvedFairOneGapOriginal_size s0 i
  have hj := resolvedFairOneGapOriginal_size s0 j
  have h := resolvedFairCodePosition_strictMono s0 hij
  dsimp only
  omega

theorem resolvedFairOneGapOriginal_injective
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    Function.Injective (resolvedFairOneGapOriginal s0) := by
  intro i j hij
  exact (resolvedFairOneGapOriginal_strictMono_size s0).injective
    (congrArg (fun v : FiniteGPlusVertex (hensonForbiddenFamily 4 (by omega)) =>
      v.val.size) hij)

/-- Both directed ordinary bits, including nonedges, at every distinct pair. -/
theorem resolvedFairOneGapOriginal_binary
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i j : Nat) (hij : i ≠ j) :
    finiteGPlusBinary (resolvedFairOneGapOriginal s0 i)
      (resolvedFairOneGapOriginal s0 j) 0 = s0.edge (2*i) (2*j) := by
  have hAddress : oneGapAddress (resolvedFairCodePosition s0 i) ≠
      oneGapAddress (resolvedFairCodePosition s0 j) := by
    intro h
    exact hij ((resolvedFairCodePosition_strictMono s0).injective
      (oneGapAddress_strictMono.injective h))
  unfold resolvedFairOneGapOriginal
  rw [CountableEnumeratedPartialStructure.toGPlus_binary _ _ _ hAddress]
  change oneGapEdge (resolvedFairChronologicalEdge s0)
    (oneGapAddress (resolvedFairCodePosition s0 i))
    (oneGapAddress (resolvedFairCodePosition s0 j)) = _
  rw [oneGapEdge_address]
  exact resolvedFairChronologicalEdge_originals s0 i j

theorem resolvedFairOneGapOriginal_diagonal
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i : Nat) :
    finiteGPlusDiagonal (resolvedFairOneGapOriginal s0 i) 0 = false := by
  unfold resolvedFairOneGapOriginal
  rw [CountableEnumeratedPartialStructure.toGPlus_diagonal]
  change oneGapEdge (resolvedFairChronologicalEdge s0)
    (oneGapAddress (resolvedFairCodePosition s0 i))
    (oneGapAddress (resolvedFairCodePosition s0 i)) = false
  rw [oneGapEdge_address]
  exact resolvedFairChronologicalEdge_loops s0 _

/-- All auxiliary atoms on the originals are their strict chronological order. -/
theorem resolvedFairOneGapOriginal_E
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i j : Nat) :
    finiteGPlusE (resolvedFairOneGapOriginal s0 i)
      (resolvedFairOneGapOriginal s0 j) = decide (i < j) := by
  unfold resolvedFairOneGapOriginal
  rw [CountableEnumeratedPartialStructure.toGPlus_E]
  change oneGapAux (oneGapAddress (resolvedFairCodePosition s0 i))
    (oneGapAddress (resolvedFairCodePosition s0 j)) = _
  simp only [oneGapAux,oneGapAddress_real,true_and]
  have hSpace : oneGapAddress (resolvedFairCodePosition s0 i) + 1 <
      oneGapAddress (resolvedFairCodePosition s0 j) ↔ i < j := by
    have hMono : resolvedFairCodePosition s0 i < resolvedFairCodePosition s0 j ↔
        i < j := (resolvedFairCodePosition_strictMono s0).lt_iff_lt
    unfold oneGapAddress
    omega
  simp only [hSpace]

/-- The actual canonical G+ source contains the prescribed K4-free graph. -/
theorem resolvedInitialOneGapOriginal_binary
    (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false)
    (i j : Nat) (hij : i ≠ j) :
    let s0 := resolvedInitialStage E hFree hSym hLoops
    finiteGPlusBinary (resolvedFairOneGapOriginal s0 i)
      (resolvedFairOneGapOriginal s0 j) 0 = E i j := by
  dsimp only
  rw [resolvedFairOneGapOriginal_binary _ i j hij]
  change E (2*i/2) (2*j/2) = E i j
  congr 1 <;> omega

end Kk
