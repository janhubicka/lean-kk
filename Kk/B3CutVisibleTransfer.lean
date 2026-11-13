import Kk.B3SmallCliqueCore
import Mathlib.Tactic

/-!
# Track D: cut-visible transfer of the *full* corrected B3 test

An arbitrary forbidden-clique continuation may contain upper vertices
with freely chosen upper--upper edges. Its clique core is nonetheless
incident with the tested cut, so only complete upper L-types whose
actual source names are adjacent to the cut can occur in this core.

This theorem transfers corrected B3 from a smaller selected pool G
to a larger selected pool F using only those *cut-visible* complete
L-reducts. The coverage hypothesis refers to the ACTUAL CHOSEN
target of G, not merely to a vertex with the same old L+ source:
the eligible-pool function deduplicates source types by choice.

The source-nonempty hypothesis is essential: an empty G source makes
G.CorrectedB3 vacuous. Neither hypothesis has been established for
the global resolved K_k diary. In particular this theorem does not
project the K4 cut-10 {q2,x} counterexample to {x}.
-/

namespace Kk

open SuccessorTree.V10

/-- A full selected-stage corrected B3 test follows from a marked
test if every cut-adjacent FULL source name has its entire next-cut
ordinary L-reduct among the MARKED pool's actually chosen outputs.

The theorem deliberately does not assume global inclusion of full
upper L-types in the marked upper spectrum: off-cut sources cannot
occur in a forbidden clique created by inserting the cut.

The Boolean original graph is the actual symmetric, loop-free,
K_ell-free source. The proof uses the genuine small clique core and
never assigns auxiliary E to an arbitrary L-only age-test witness. -/
theorem henson_fullB3_of_cut_visible_complete_outputs
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Full Marked : Fin M → Prop)
    (hMarkedNonempty :
      ∃ T, T ∈ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).source)
    (hCutVisible : ∀ v : Fin M, Full v →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true →
      ∃ T, T ∈ (selectedStagePoolPrescribedData
          (finiteNumericH (normalizedGraphModel E) k N)
          cut original Marked).source ∧
        ((selectedStagePoolPrescribedData
          (finiteNumericH (normalizedGraphModel E) k N)
          cut original Marked).target T).lReduct =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL (normalizedGraphModel E) k N)
            (cut+1) (original v).val)
    (hMarked :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Full).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  classical
  let A := finiteNumericH (normalizedGraphModel E) k N
  let C := finiteNumericHL (normalizedGraphModel E) k N
  let G := selectedStagePoolPrescribedData A cut original Marked
  by_contra hFailure
  obtain ⟨V,e,hFinite,hSocle,hDelete,hUpper,hCopy,hAt,hFuture⟩ :=
    henson_selectedB3_failure_has_small_clique_core
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full hFailure
  obtain ⟨S,hS⟩ := hMarkedNonempty
  obtain ⟨v0,_hv0,_hFree0,_hOld0,hTarget0⟩ :=
    selectedStagePoolPrescribedData_source_original
      A cut original Marked S hS
  have hSocleG :
      SameInitialL (prescribedOrdinarySocle (G.target S)) C cut := by
    rw [show G.target S = A.partialTypeAt (cut+1) (original v0).val
          from hTarget0]
    exact ambient_partialType_prescribedSocle A cut
      (original v0).val hCut
  have hSocleReverse :
      SameInitialL C (prescribedOrdinarySocle (G.target S)) cut := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      exact (hSocleG.1 x hx).symm
    · intro x y hx hy t
      exact (hSocleG.2.1 x y hx hy t).symm
    · intro x hx t
      exact (hSocleG.2.2.1 x hx t).symm
    · intro x hx t
      exact (hSocleG.2.2.2 x hx t).symm
  have hMatched :
      SameInitialL V (prescribedOrdinarySocle (G.target S)) cut :=
    hSocle.trans hSocleReverse
  have hUpperMarked :
      UpperTypesPrescribed V cut G.PrescribedUpperLType := by
    intro x hx hAbove
    obtain ⟨a,ha⟩ := hFuture x hx hAbove
    obtain ⟨v,hFull,_hFree,hType⟩ := hUpper x hx hAbove
    obtain ⟨b,hb⟩ := hAt
    have hba : b ≠ a := by
      intro hEq
      have hxEq : x = cut := by
        calc
          x = e a := ha.symm
          _ = e b := by rw [hEq]
          _ = cut := hb
      omega
    have hWEdge : V.binary cut x (0 : Fin 1) = true := by
      have hEdge := hCopy.2.2.1 b a hba (0 : Fin 1)
      have hAtEdge : V.binary cut (e a) (0 : Fin 1) = true := by
        simpa [hb,cliquePattern,hba] using hEdge
      simpa [ha] using hAtEdge
    have hCross := congrArg
        (fun T : RelationalPrefixType (cut+1) 1 0 1 =>
          T.binary
            (some (⟨cut,Nat.lt_succ_self cut⟩ : Fin (cut+1)))
            none (0 : Fin 1)) hType
    change V.binary cut x (0 : Fin 1) =
      C.binary cut (original v).val (0 : Fin 1) at hCross
    have hActualEdge :
        C.binary cut (original v).val (0 : Fin 1) = true :=
      hCross.symm.trans hWEdge
    obtain ⟨T,hT,hTargetType⟩ :=
      hCutVisible v hFull hActualEdge
    exact ⟨T,hT,hType.trans hTargetType.symm⟩
  have hCliqueMember :
      (NormalizedForbidden.nontrivial ell
        (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell)) ∈
          hensonForbiddenFamily ell hell := by
    simp [hensonForbiddenFamily]
  have hNoClique :
      (NormalizedForbidden.nontrivial ell
        (cliquePattern ell) (by omega)
        (cliquePattern_irreducible ell)).Avoids V :=
    hMarked S hS V hFinite hMatched hUpperMarked
      hDelete _ hCliqueMember
  have hNoCopy : ¬ ∃ f : Fin ell → Nat,
      V.Realizes (cliquePattern ell) f :=
    ((NormalizedForbidden.nontrivial ell
      (cliquePattern ell) (by omega)
      (cliquePattern_irreducible ell)).signaturePattern_avoids_iff V).1
        hNoClique
  exact hNoCopy ⟨e,hCopy⟩

/-- The logically equivalent failure-projection formulation.

This is useful when proving that an alleged marked boring level cannot
hide a genuine full parameter-closed forbidden clique. The complete
cut-visible target coverage remains a *hypothesis*, not a proved diary
invariant. -/
theorem henson_cut_visible_fullB3_failure_implies_marked_failure
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N)
    (original : Fin M → Fin N)
    (Full Marked : Fin M → Prop)
    (hMarkedNonempty :
      ∃ T, T ∈ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).source)
    (hCutVisible : ∀ v : Fin M, Full v →
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true →
      ∃ T, T ∈ (selectedStagePoolPrescribedData
          (finiteNumericH (normalizedGraphModel E) k N)
          cut original Marked).source ∧
        ((selectedStagePoolPrescribedData
          (finiteNumericH (normalizedGraphModel E) k N)
          cut original Marked).target T).lReduct =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL (normalizedGraphModel E) k N)
            (cut+1) (original v).val)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Full).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ¬ (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Marked).CorrectedB3
        (hensonForbiddenFamily ell hell) := by
  intro hMarked
  exact hFailure
    (henson_fullB3_of_cut_visible_complete_outputs
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original Full Marked
      hMarkedNonempty hCutVisible hMarked)

#print axioms henson_fullB3_of_cut_visible_complete_outputs
#print axioms henson_cut_visible_fullB3_failure_implies_marked_failure

end Kk
