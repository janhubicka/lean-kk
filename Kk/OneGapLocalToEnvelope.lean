import Kk.OneGapStructuralExclusion
import Kk.OneGapPrescribedPool

/-!
# Actual planned envelopes from selected ordinary neutrality

The hypotheses below are explicit ordinary source, age and endpoint
conditions. The proof constructs the complete prescribed crossing data,
its corrected B3 certificate and each skipping map before performing the
descending envelope induction.

See `docs/one_gap_local_to_envelope_english_audit_20261126.md`.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

/-- Discharge the full local Kpt obligations from selected ordinary data,
then construct an envelope with precisely the planned retained levels.
The selected labelled list may vary with the cut. -/
theorem oneGap_planned_envelope_of_selected_neutrality
    (ell : Nat) (hell : 2 ≤ ell)
    (A : EnumeratedPartialStructure 1 0 1)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell → bad.Avoids A.L)
    (hSym : ∀ x y, A.L.binary x y (0 : Fin 1) = A.L.binary y x (0 : Fin 1))
    (hLoop : ∀ x, A.L.binary x x (0 : Fin 1) = false)
    (hDiag : ∀ x, A.L.diagonal x (0 : Fin 1) = false)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (top : Nat) (hTopSize : top < A.size) (hXBound : X ⊆ levelLe top)
    (I : Set Nat) (hZero : 0 ∈ I) (hTop : top ∈ I)
    (hBound : ∀ q ∈ I, q ≤ top)
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool (hensonForbiddenFamily ell hell) A hAvoid U)
    (hUV : U ⊆ V)
    (hRet : ∀ i : Fin A.size, i.val ∈ I → 0 < A.freeLevel i.val → i ∈ V)
    (hSeedRet : ∀ z ∈ X, LevelTree.lev z ∈ I)
    (hEndRet : ∀ v ∈ V, A.freeLevel v.val ∈ I)
    (d : Nat → Nat) (selected : (c : Nat) → Fin (d c) → Nat)
    (hPositive : ∀ c, c < top → c ∉ I →
      ∀ v ∈ V, c+1 ≤ A.freeLevel v.val →
        A.L.binary c v.val 0 = true → ∃ j, v.val = selected c j)
    (hNoSplit : ∀ c, c < top → c ∉ I → ∀ i j : Fin (d c),
      c < selected c i → c < selected c j →
      (∀ p < c, A.L.binary p (selected c i) 0 = A.L.binary p (selected c j) 0) →
      A.L.binary c (selected c i) 0 = A.L.binary c (selected c j) 0)
    (hOtherZero : ∀ c, c < top → c ∉ I →
      ∀ v ∈ V, c+1 ≤ A.freeLevel v.val →
      (¬ ∃ j, v.val = selected c j) →
      ∀ p < c, A.L.binary p v.val 0 = false)
    (hAge : ∀ c, c < top → c ∉ I → ∀ T : IntegerGraphSupport (d c) ell,
      integerGraphAgeCanonical (d c) ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell (d c)
          (Finset.range c) (fun p j => A.L.binary p (selected c j) 0)) T =
      integerGraphAgeCanonical (d c) ell
        (finiteOldColumnRawBound (fun x y => A.L.binary x y 0) ell (d c)
          (Finset.range (c+1)) (fun p j => A.L.binary p (selected c j) 0)) T) :
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily ell hell)),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily ell hell))
        X top 0 I F ∧
      F.map.levelRange = {q | q ∈ I ∨ top < q} := by
  let family := hensonForbiddenFamily ell hell
  have hLocal : ∀ c : Nat, c < top → c ∉ I →
      let Z := closure (admissibleKptSTree family) {q | q ∈ I ∧ c+1 ≤ q} X
      (∀ z ∈ Z, LevelTree.lev z ≠ c) ∧
        ∃ F : PrescribedBoringData c 1 0 1,
          CoversClosureCrossing family Z c F ∧
          (∀ S, S ∈ F.source → IsAdmissibleRawType family
            (⟨c+1,F.target S⟩ : RawPartialTypeNode 1 0 1)) ∧
          F.CorrectedB3 family := by
    intro c hc hNot
    have hFibre := oneGap_full_fibre_of_selected_neutrality
      A ell (d c) c hell V (selected c) hSym hLoop hDiag
      (hPositive c hc hNot) (hNoSplit c hc hNot)
      (hOtherZero c hc hNot) (hAge c hc hNot)
    have hRetStage : ∀ i : Fin A.size,
        i.val ∈ {q | q ∈ I ∧ c+1 ≤ q} → 0 < A.freeLevel i.val → i ∈ V :=
      fun i hi => hRet i hi.1
    have hSeed : ∀ z ∈ X, LevelTree.lev z ≠ c := by
      intro z hz heq
      exact hNot (heq ▸ hSeedRet z hz)
    have hEnd : ∀ v ∈ V, A.freeLevel v.val ≠ c := by
      intro v hv heq
      exact hNot (heq ▸ hEndRet v hv)
    have hStructural := oneGap_planned_closure_structural_of_full_fibre
      family A hAvoid {q | q ∈ I ∧ c+1 ≤ q} X U V
      hX hUV hRetStage c hSeed hEnd hFibre
    refine ⟨?_,oneGapRetainedPoolData A c V,?_,?_,?_⟩
    · intro z hz hlev
      exact hStructural.1 ⟨z,hz,hlev⟩
    · exact oneGapRetainedPoolData_covers_planned_closure family A hAvoid
        c {q | q ∈ I ∧ c+1 ≤ q} X U V hX hUV hRetStage hFibre
    · exact oneGapRetainedPoolData_targets_admissible family A hAvoid c V
    · exact oneGapRetainedPoolData_correctedB3_all ell hell (d c) c
        A (by omega) hAvoid hSym V (selected c)
        (hPositive c hc hNot) (hAge c hc hNot)
  obtain ⟨F,hF⟩ := oneGap_planned_Kpt_envelope family X top hXBound
    I hZero hTop hBound hLocal
  refine ⟨F,hF,?_⟩
  simpa only [Nat.not_lt_zero, false_or] using
    stageFullInvariant_levelRange (normalizedKptSMTree family) X top 0 I F hF

end Kk
